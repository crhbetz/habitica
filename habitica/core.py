#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
Phil Adams http://philadams.net

habitica: commandline interface for http://habitica.com
http://github.com/philadams/habitica

TODO:philadams add logging to .api
TODO:philadams get logger named, like requests!
"""


from bisect import bisect
import json
import logging
import os.path
import random
import sys
from operator import itemgetter
import re
from time import sleep, time
from webbrowser import open_new_tab

from collections import OrderedDict
import datetime
import humanize
import dateutil.parser
import pytz
import textwrap

from docopt import docopt

from . import api

from pprint import pprint

try:
    import ConfigParser as configparser
except:
    import configparser


VERSION = 'habitica version 0.0.16'
TASK_VALUE_BASE = 0.9747  # http://habitica.wikia.com/wiki/Task_Value
HABITICA_REQUEST_WAIT_TIME = 0.5  # time to pause between concurrent requests
HABITICA_TASKS_PAGE = '/#/tasks'
# https://trello.com/c/4C8w1z5h/17-task-difficulty-settings-v2-priority-multiplier
PRIORITY = {'easy': 1,
            'medium': 1.5,
            'hard': 2}
AUTH_CONF = os.path.expanduser('~') + '/.config/habitica/auth.cfg'
CACHE_CONF = os.path.expanduser('~') + '/.config/habitica/cache.cfg'
SETTINGS_CONF = os.path.expanduser('~') + '/.config/habitica/settings.cfg'

SECTION_HABITICA = 'Habitica'
SECTION_CACHE_QUEST = 'Quest'
SECTION_CACHE_GUILDNAMES = 'Guildnames'
checklists_on = False

DEFAULT_PARTY = 'Not currently in a party'
DEFAULT_QUEST = 'Not currently on a quest'
DEFAULT_PET = 'No pet currently'
DEFAULT_MOUNT = 'Not currently mounted'

def load_typo_check(config, defaults, section, configfile):
    for item in config.options(section):
        if item not in defaults:
            raise ValueError("Option '%s' (section '%s') in '%s' not known!"
                             % (item, section, configfile))

def load_settings(configfile):
    """Get settings data from the SETTINGS_CONF file."""

    logging.debug('Loading habitica settings data from %s' % configfile)

    integers = {'sell-max': "-1",
                'sell-reserved': "-1",
                'eggs-extra': "0",
               }
    strings = { }
    defaults = integers.copy()
    defaults.update(strings)

    config = configparser.SafeConfigParser(defaults)
    config.read(configfile)

    if not config.has_section(SECTION_HABITICA):
        config.add_section(SECTION_HABITICA)

    load_typo_check(config, defaults, SECTION_HABITICA, configfile)

    settings = {}
    for item in integers:
        settings[item] = int(config.get(SECTION_HABITICA, item))
    for item in strings:
        settings[item] = config.get(SECTION_HABITICA, item)

    return settings


def load_auth(configfile):
    """Get authentication data from the AUTH_CONF file."""

    logging.debug('Loading habitica auth data from %s' % configfile)

    try:
        cf = open(configfile)
    except IOError:
        logging.error("Unable to find '%s'." % configfile)
        exit(1)

    config = configparser.SafeConfigParser({'checklists': False})
    config.readfp(cf)

    cf.close()

    # Config name to authentication name mapping
    mapping = {'url': 'url',
               'login': 'x-api-user',
               'password': 'x-api-key',
               'checklists': 'checklists'
              }

    # Get data from config
    rv = {}
    try:
        rv = {'url': config.get('Habitica', 'url'),
              'checklists': config.get('Habitica', 'checklists'),
              'x-api-user': config.get('Habitica', 'login'),
              'x-api-key': config.get('Habitica', 'password')}
        for item in mapping:
            rv[mapping[item]] = config.get(SECTION_HABITICA, item)

    except configparser.NoSectionError:
        logging.error("No '%s' section in '%s'" % (SECTION_HABITICA,
                                                   configfile))
        exit(1)

    except configparser.NoOptionError as e:
        logging.error("Missing option in auth file '%s': %s"
                      % (configfile, e.message))
        exit(1)

    # Do this after checking for the section.
    load_typo_check(config, mapping, SECTION_HABITICA, configfile)

    # Return auth data as a dictionnary
    return rv


def load_cache(configfile):
    logging.debug('Loading cached config data (%s)...' % configfile)

    defaults = {'quest_key': '',
                'quest_s': 'Not currently on a quest'}

    cache = configparser.ConfigParser(defaults)
    cache.read(configfile)

    if not cache.has_section(SECTION_CACHE_QUEST):
        cache.add_section(SECTION_CACHE_QUEST)

    if not cache.has_section(SECTION_CACHE_GUILDNAMES):
        cache.add_section(SECTION_CACHE_GUILDNAMES)

    return cache


def update_quest_cache(configfile, **kwargs):
    logging.debug('Updating (and caching) config data (%s)...' % configfile)

    cache = load_cache(configfile)

    for key, val in kwargs.items():
        cache.set(SECTION_CACHE_QUEST, key, val)

    with open(configfile, 'w') as f:
        cache.write(f)

    cache.read(configfile)

    return cache

def update_guildnames_cache(configfile, number, name):
    logging.debug('Updating (and caching) config data (%s)...' % configfile)

    cache = load_cache(configfile)

    cache.set(SECTION_CACHE_GUILDNAMES, number, name)

    with open(configfile, 'w') as f:
        cache.write(f)

    cache.read(configfile)

    return cache



def get_task_ids(tids):
    """
    handle task-id formats such as:
        habitica todos done 3
        habitica todos done 1,2,3
        habitica todos done 2 3
        habitica todos done 1-3,4 8
    tids is a seq like (last example above) ('1-3,4' '8')
    """
    logging.debug('raw task ids: %s' % tids)
    task_ids = []
    for raw_arg in tids:
        for bit in raw_arg.split(','):
            if '-' in bit:
                start, stop = [int(e) for e in bit.split('-')]
                task_ids.extend(range(start, stop + 1))
            else:
                task_ids.append(int(bit))
    return [e - 1 for e in set(task_ids)]


def nice_name(thing):
    if '_' in thing:
        thing = thing.replace('_', '-')
    prettied = " ".join(thing.split('-')[::-1])
    # split camel cased words
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)',
                        prettied)
    prettier = ' '.join([m.group(0).title() for m in matches])
    return prettier


def find_pet_to_feed(pets, items, suffix, finicky):
    basic = [ 'BearCub', 'Cactus', 'Dragon', 'FlyingPig',
              'Fox', 'LionCub', 'PandaCub', 'TigerCub', 'Wolf' ]
    rare = [ 'Wolf-Veteran', 'Wolf-Cerberus', 'Dragon-Hydra',
             'Turkey-Base', 'BearCub-Polar', 'MantisShrimp-Base',
             'JackOLantern-Base', 'Mammoth-Base', 'Tiger-Veteran',
             'Phoenix-Base', 'Turkey-Gilded' ]

    mouth = None
    best = 0
    for pet in pets:
        fed = items['pets'][pet]

        # Unhatched pet.
        if fed <= 0:
            #print("Unhatched: %s" % (pet))
            continue
        # Unfeedable pet.
        if pet in rare:
            continue
        if items['mounts'].get(pet, 0) == 1 and fed == 5:
            #print("Has mount: %s" % (pet))
            continue
        # Not best food match.
        if finicky and not pet.endswith('-%s' % (suffix)):
            #print("Not a match for %s: %s" % (food, pet))
            continue

        # Feed the pet that is closest to becoming a mount.
        if fed > best:
            best = fed
            mouth = pet
        elif fed == best:
            # In the case of a tie, prefer feeding basic pets
            # to get Pet achievement.
            if pet in basic:
                mouth = pet
    return mouth

def updated_task_list(tasks, tids):
    for tid in sorted(tids, reverse=True):
        del(tasks[tid])
    return tasks


def cl_done_count(task):
    items = task['checklist']
    count = 0
    for li in items:
        if li['completed'] == True:
            count = count + 1
    return count


def cl_item_count(task):
    if 'checklist' in task:
        return len(task['checklist'])
    else:
        return 0


def print_task_list(tasks):
    longesttext = 0
    for task in tasks:
        if len(task['text']) > longesttext:
            longesttext = len(task['text'])
    for i, task in enumerate(tasks):
        if task['completed']:
            completed = 'x'
        elif task['type'] == "todo":
            completed = '_'
        elif 'isDue' in task.keys() and task['isDue']:
            completed = '_'
        else:
            completed = '/'
        streak = '*%s' % (task['streak']) if 'streak' in task else ''
        task_line = '[%s] %s %s\t%s' % (completed,
                                         i + 1,
                                         streak,
                                         task['text'])
        checklist_available = cl_item_count(task) > 0
        if checklist_available:
            rjust_todo = len(task_line) - len(task['text'])
            task_line += ' (%s/%s)' % (str(cl_done_count(task)),
                                       str(cl_item_count(task)))
        if task['type'] == "todo" and 'date' in task.keys() and task['date'] != "":
            task_line = task_line.ljust(longesttext + 9)
            task_line += 'due %s (%s)' % (humanize.naturaltime(datetime.datetime.now(pytz.utc) - \
                                                datetime.timedelta(days=1) - \
                                                dateutil.parser.parse(task['date'])\
                                                .astimezone(dateutil.tz.tzlocal())),
                                            humanize.naturaldate(dateutil.parser.parse(task['date'])\
                                                .astimezone(dateutil.tz.tzlocal())))
        print(task_line)
        if checklists_on and checklist_available:
            for c, check in enumerate(task['checklist']):
                completed = 'x' if check['completed'] else '_'
                print('%s%s [%s] %s' % ('\t'.rjust(rjust_todo),
                                     chr(ord('a') - 1 + c + 1),
                                     completed,
                                     check['text']))


def qualitative_task_score_from_value(value):
    # task value/score info: http://habitica.wikia.com/wiki/Task_Value
    scores = ['*', '**', '***', '****', '*****', '******', '*******']
    breakpoints = [-20, -10, -1, 1, 5, 10]
    return scores[bisect(breakpoints, value)]

def get_currency(gp, balance="0.0"):
    gem = int(float(balance) * 4)
    gp = float(gp)
    gold = int(gp)
    silver = int((gp - int(gp)) * 100)
    report = ''
    if gem > 0:
        report += '%d Gem%s, ' % (gem, "" if gem == 1 else "s")
    report += '%d Gold' % (gold)
    if silver > 0:
        report += ', %d Silver' % (silver)
    return report

max_report = { 'exp': {'title':'Experience', 'max':'toNextLevel',
                                             'maxValue': "0"},
               'hp':  {'title':'Health', 'max':'maxHealth',
                                         'maxValue': "50"},
               'mp':  {'title':'Mana', 'max':'maxMP',
                                       'maxValue': "100"},
             }

# XXX: This is a hack to refresh the current stats to find maxes,
# which are sometimes missing for some reason.
def fix_max(hbt, item, bstats, astats, refresh=True):
    if astats.get(max_report[item]['max'], None) == None:
        # If max exists in "before" stats, use it instead.
        if bstats.get(max_report[item]['max'], None) != None:
            astats[max_report[item]['max']] = bstats[max_report[item]['max']]
        elif refresh and item != 'hp':
            # Perform full refresh and update all report items.
            refresh = hbt.user()
            rstats = refresh.get('stats', [])
            for fixup in max_report:
                astats[max_report[fixup]['max']] = rstats[max_report[fixup]['max']]
        else:
            # Either no refresh wanted, or max HP is missing which is static.
            astats[max_report[item]['max']] = max_report[item]['maxValue']
    return astats

def show_delta(hbt, before, after):
    bstats = before.get('stats', [])
    astats = after.get('stats', [])
    bitems = before.get('items', [])
    aitems = after.get('items', [])

    for item in max_report:
        delta = int(astats[item] - bstats[item])
        if delta != 0:
            # XXX: hack to fix max entry.
            astats = fix_max(hbt, item, bstats, astats)

            print('%s: %d (%d/%d)' % (max_report[item]['title'],
                                      delta, int(astats[item]),
                                      int(astats.get(max_report[item]['max'],
                                                     "0"))))

    # Currency
    bgp = float(bstats.get('gp', "0.0"))
    agp = float(astats.get('gp', "0.0"))
    gp = agp - bgp
    bgems = float(before.get('balance', "0.0"))
    agems = float(after.get('balance', "0.0"))
    gems = agems - bgems
    if gp != 0.0 or gems != 0.0:
        print("%s" % (get_currency(gp, gems)))

    # Pets
    apets = aitems['pets']
    bpets = bitems['pets']
    for pet in apets:
        if bpets.get(pet, 0) <= 0 and apets[pet] > 0:
            print("Hatched %s" % (nice_name(pet)))

    # Food
    afood = aitems['food']
    bfood = bitems['food']
    for food in afood:
        if afood.get(food, 0) > bfood.get(food, 0):
            print("Received %s" % (nice_name(food)))

    # Mounts
    amounts = aitems['mounts']
    bmounts = bitems['mounts']
    for mount in amounts:
        if bmounts.get(mount, '') != amounts[mount] and amounts[mount] > 0:
            print("Metamorphosed a %s" % (nice_name(mount)))

    # Equipment
    bequip = bitems['gear']['equipped']
    aequip = aitems['gear']['equipped']
    for location, item in aequip.items():
        if bequip.get(location, '') != item:
            print("%s now has %s" % (location, item))


def do_item_enumerate(user, requested, ordered=False, pretty=True):
    counted = False
    items = user.get('items', [])
    if len(requested) == 0:
        for item in items:
            # Attempt to figure out if this is a dict of dicts or not.
            try:
                if isinstance(items[item], dict):
                    one = items[item].keys()[0]
                    if isinstance(items[item][one], dict):
                        for thing in items[item]:
                            print('%s/%s' % (item, thing))
                        continue
            except:
                pass
            print('%s' % (item))
        return

    results = {}
    for name in requested:
        if '/' in name:
            main, sub = name.split('/', 1)
            items = items.get(main, {sub: []})
            name = sub

        available = items.get(name, [])
        #print(available)
        if len(available) == 0:
            print("You don't have any %s!" % (name))
            continue
        if isinstance(available, str):
            # This is a singleton, so disable counting.
            counted = False
            if pretty:
                result_name = nice_name(available)
            else:
                result_name = available
            results[result_name] = 1
        elif isinstance(available, dict):
            for item in available:
                if pretty:
                    result_name = nice_name(item)
                else:
                    result_name = item

                if isinstance(items[name][item], bool):
                    # If false, we may want to skip it...
                    #continue
                    value = True
                elif isinstance(items[name][item], str):
                    result_name += ": %s" % (items[name][item])
                    value = True
                elif isinstance(items[name][item], int):
                    # This is an integer item, so count them.
                    counted = True
                    value = items[name][item]
                else:
                    # Include unknown type in results.
                    result_name += " %s" % (str(type(items[name][item])))
                    value = True

                if value:
                    results[result_name] = value
        else:
            print("Don't know how to show %s" % (str(type(available))))
            sys.exit(1)

    if counted:
        if ordered:
            for i, c in sorted(results.items(), key=itemgetter(1)):
                print('%s: %d' % (i, c))
        else:
            for item in results:
                print('%s: %d' % (item, results[item]))
    else:
        if ordered:
            for i, c in sorted(results.items(), key=itemgetter(0)):
                print('%s' % (i))
        else:
            for item in results:
                print('%s' % (item))

def get_members(auth, party):
    result = []
    group = api.Habitica(auth=auth, resource="groups", aspect=party['id'])
    members = group(_one='members')
    for i in members:
        member = api.Habitica(auth=auth, resource="members", aspect=i['id'])()
        result.append(member)
    return result

def stat_down(hbt, user, stat, amount):
    stats = user.get('stats', [])
    stats = fix_max(hbt, stat, stats, stats, refresh=False)
    down = int(stats.get(max_report[stat]['max'],"0")) - int(stats[stat])
    print("%s has %d/%d %s" % (user['profile']['name'], int(stats[stat]),
                               int(stats[max_report[stat]['max']]),
                               max_report[stat]['title']))
    if down >= amount:
        return True
    return False

def party_hp_down_ten(auth, hbt, user, party=None, myself=False):
    needs_healing = False
    down = False
    if party == None:
        party = hbt.groups.party()
    if not myself:
        members = get_members(auth, party)
    else:
        members = [user]
    for member in members:
        if stat_down(hbt, member, 'hp', 10):
            print("%s needs healing" % (member['profile']['name']))
            needs_healing = True
    if needs_healing:
        return

    print("Already in good health!")
    sys.exit(1)

def hp_down_ten(auth, hbt, user):
    # Do a party check, but just a party of myself.
    party_hp_down_ten(hbt, user, myself=True)


def set_checklists_status(auth, args):
    """Set display_checklist status, toggling from cli flag"""
    global checklists_on

    if auth['checklists'] == "true":
        checklists_on = True
    else:
        checklists_on = False

    # reverse the config setting if specified by the CLI option
#    if args['--checklists']:
#        checklists_on = not checklists_on

    return

def isChecklistItem(tid):
#    checklist = re.compile(r'^[0-9][a-z]$')
    if re.search(r'^[0-9]+[a-z]$', tid) != None:
        number = ord(re.search(r'[a-z]', tid).group(0)) - 97 #for char in re.findall(r'[a-z]{1}', tid)
        ttid = int(re.match(r'[0-9]+', tid).group(0)) - 1
        logging.debug('found checklist item, number %s of task %s' 
                      % (number, ttid))
        return ttid, number
    elif re.search(r'^[0-9]+$', tid) != None:
        logging.debug('false')
        return False
    else:
        logging.debug('None')
        return None

def group_user_status(quest_data, auth, hbt):
    groupUserStatus = {}
    groupUserStatus['users'] = {}
    groupUserStatus['queststatus'] = quest_data['active']
    for user in quest_data['members'].keys():
        groupUserStatus['users'][user] = {}
        member = getattr(hbt.members, user)()
        groupUserStatus.setdefault('longestname', 1)
        if len(member['profile']['name']) > groupUserStatus['longestname']:
                groupUserStatus['longestname'] = len(member['profile']['name'])
        groupUserStatus['users'][user]['name'] = member['profile']['name']
        if quest_data['members'][user] == True:
                groupUserStatus['users'][user]['decision'] = 'accepted'
        elif quest_data['members'][user] == False:
                groupUserStatus['users'][user]['decision'] = 'denied'
        else:
                groupUserStatus['users'][user]['decision'] = 'waiting'
        if member['preferences']['sleep']:
                groupUserStatus['users'][user]['sleep'] = 'sleeping'
        else:
                groupUserStatus['users'][user]['sleep'] = 'active'
        groupUserStatus['users'][user]['lastactive'] = member['auth']['timestamps']['loggedin']
        stats = ['hp', 'maxHealth', 'mp', 'maxMP', 'class']
        for stat in stats:
            groupUserStatus['users'][user][stat] = member['stats'][stat]
        
    groupUserStatus['users'] = OrderedDict(sorted(groupUserStatus['users'].items(), key=lambda t: t[1]['lastactive']))
    return groupUserStatus


def print_gus(groupUserStatus, len_ljust):
    len_ljust += 1
    headLine = ' '.rjust(len_ljust, ' ')
    headLine += 'Name'.ljust(groupUserStatus['longestname'] + 1)
    headLine += 'Class'.ljust(9, ' ')
    if not groupUserStatus['queststatus']:
        headLine += 'Answer'.ljust(10, ' ')
    headLine += 'Status'.ljust(9, ' ')
    headLine += 'Last login'.ljust(14, ' ')
    headLine += 'Health'.ljust(8, ' ')
    headLine += 'Mana'.ljust(8, ' ')
    print(headLine)

    print(' '.rjust(len_ljust, ' ') + '-' * (len(headLine) - len_ljust)) #(groupUserStatus['longestname'] + 19 + 14))

    for user in groupUserStatus['users'].values():
        userLine = ' '.rjust(len_ljust, ' ')
        userLine += user['name'].ljust(groupUserStatus['longestname'] + 1)
        userLine += user['class'].capitalize().ljust(9, ' ') 
        if not groupUserStatus['queststatus']:
            userLine += user['decision'].ljust(10, ' ')
        userLine += user['sleep'].ljust(9, ' ')
        userLine += humanize.naturaltime(datetime.datetime.now(pytz.utc) - dateutil.parser.parse(user['lastactive'])).ljust(14, ' ')
        userLine += (str(int(user['hp'])) + '/' + str(user['maxHealth'])).ljust(8, ' ')
        userLine += (str(int(user['mp'])) + '/' + str(user['maxMP'])).ljust(8, ' ')
        print(userLine)

def chatID(party, user, guilds):
    message = ('Invalid ID - must be 0 for party or > 0.\n'
              'Use \'habitica chat list\' to get a list of IDs.')
    try:
        party = int(party)
    except ValueError:
        print(message)
        sys.exit(1)

    if party > 0:
         try:
             party = guilds[int(party)-1]
             return party
         except IndexError:
             print('ID too high - you\'re not a member '
                   'in this many guilds.')
             sys.exit(1)
    elif party == 0:
         party = user.get('party')['_id']
         return party
    else:
        print(message)
        sys.exit(1)

def printChatMessages(messages, messageNum):
    messages = sorted(messages, key=lambda k: k['timestamp']) 
    messages = messages[-messageNum:]
    for message in messages:
        name = message['user'] if 'user' in message.keys() else 'System'
        timestamp = int(str(message['timestamp'])[0:10])
        print('\n%s, %s:\n%s' % (name,
                                humanize.naturaltime(datetime.datetime.now() \
                                - datetime.datetime.fromtimestamp(timestamp)),
                                textwrap.fill(message['text'], width=80)))


def cli():
    """Habitica command-line interface.

  Usage: habitica [--version] [--help]
                  <command> [<args>...] [--difficulty=<d>]
                  [--verbose | --debug]

  Options:
    -h --help         Show this screen
    --version         Show version
    --difficulty=<d>  (easy | medium | hard) [default: easy]
    --verbose         Show some logging information
    --debug           Some all logging information

  The habitica commands are:
    status                     Show HP, XP, GP, and more
    habits                     List habit tasks
    habits up <task-id>        Up (+) habit <task-id>
    habits down <task-id>      Down (-) habit <task-id>
    dailies                    List daily tasks
    dailies done               Mark daily <task-id> complete
    dailies undo               Mark daily <task-id> incomplete
    todos                      List todo tasks
    todos done <task-id>       Mark one or more todo <task-id> completed
    todos add <task>           Add todo with description <task>
    server                     Show status of Habitica service
    home                       Open tasks page in default browser
    item                       Show list of item types
    item <type>                Show all items of given <type>
    feed                       Feed all food to matching pets
    hatch                      Use potions to hatch eggs, sell unneeded eggs
    sell                       Show list of all potions
    sell all [<max>]           Sell all hatching potions (up to <max> many)
    sell <type> [<max>]        Sell all <type> hatching potions (up to <max>)
    cast                       Show list of castable spells
    cast <spell> [<id>]        Cast <spell> (on task <id>)
    cast smart <spell> [<id>]  After smart-check, cast <spell> (on task <id>)
    gems                       Buy gems until you can't
    armoire                    Buy something from the armoire
    walk                       List available pets to walk
    walk <pet>                 Walk (equip) the <pet> pet
    walk random                Walk (equip) a random pet
    ride                       List available mounts
    ride <mount>               Ride (equip) the <mount> mount
    ride random                Ride (equip) a random mount
    equip <gear>               Equip a piece of gear
    sleep                      Rest in the inn
    arise                      Check out of the inn
    quest                      Report quest details
    quest accept               Accept a quest proposal
    chat list                  List available chats and their ID
    chat show [<id>] [<num>]   Shows last <num> messages from chat <id>
                               (defaults: ID 0, num 5)
    chat send <id> "<Message>" Sends Message to chat ID 

  For `habits up|down`, `dailies done|undo`, and `todos done`, you can pass
  one or more <task-id> parameters, using either comma-separated lists or
  ranges or both. For example, `todos done 1,3,6-9,11`.
  """

    # set up args
    args = docopt(cli.__doc__, version=VERSION)

    # set up logging
    if args['--verbose']:
        logging.basicConfig(level=logging.INFO)
    if args['--debug']:
        logging.basicConfig(level=logging.DEBUG)

    logging.debug('Command line args: {%s}' %
                  ', '.join("'%s': '%s'" % (k, v) for k, v in args.items()))

    # list of kinds of pets/potions (disregarding Magic Potion ones)
    kinds = [ 'Base', 'CottonCandyBlue', 'CottonCandyPink', 'Golden',
              'White', 'Red', 'Shade', 'Skeleton', 'Desert', 'Zombie' ]

    # Set up auth
    auth = load_auth(AUTH_CONF)

    # Prepare cache
    cache = load_cache(CACHE_CONF)

    # Load settings
    settings = load_settings(SETTINGS_CONF)

    # instantiate api service
    hbt = api.Habitica(auth=auth)

    # Flag checklists as on if true in the config
    set_checklists_status(auth, args)

    # GET server status (v3 ok)
    if args['<command>'] == 'server':
        server = hbt.status()
        if server['status'] == 'up':
            print('Habitica server is up')
        else:
            print('Habitica server down... or your computer cannot connect')

    # open HABITICA_TASKS_PAGE (v3 ok)
    elif args['<command>'] == 'home':
        home_url = '%s%s' % (auth['url'], HABITICA_TASKS_PAGE)
        print('Opening %s' % home_url)
        open_new_tab(home_url)

    # GET item lists (v3 ok)
    elif args['<command>'] == 'item':
        user = hbt.user()
        do_item_enumerate(user, args['<args>'])

    # Feed all possible animals (v3 ok)
    elif args['<command>'] == 'feed':
        feeding = {
                    'Saddle':           'ignore',
                    'Meat':             'Base',
                    'CottonCandyBlue':  'CottonCandyBlue',
                    'CottonCandyPink':  'CottonCandyPink',
                    'Honey':            'Golden',
                    'Milk':             'White',
                    'Strawberry':       'Red',
                    'Chocolate':        'Shade',
                    'Fish':             'Skeleton',
                    'Potatoe':          'Desert',
                    'RottenMeat':       'Zombie',
                  }

        user = hbt.user()
        refreshed = True

        attempted_foods = set()
        fed_foods = set()

        while refreshed:
            refreshed = False
            items = user.get('items', [])
            foods = items['food']
            pets = items['pets']
            mounts = items['mounts']

            magic_pets = []
            for pet in pets:
                if pet.split('-')[1] in ['Spooky', 'Peppermint', 'Floral',
                        'Thunderstorm', 'Ghost']:
                    magic_pets.append(pet)

            for food in foods:
                # Handle seasonal foods that encode matching pet in name.
                if '_' in food:
                    best = food.split('_',1)[1]
                    if not food in feeding:
                        feeding[food] = best

                # Skip foods we don't have any of.
                if items['food'][food] <= 0:
                    continue

                # Find best pet to feed to.
                suffix = feeding.get(food, None)
                if suffix == None:
                    print("Unknown food: %s" % (food))
                    continue
                if suffix == 'ignore':
                    continue

                # Track attempted foods
                attempted_foods.add(food)

                mouth = find_pet_to_feed(pets, items, suffix, True)

                # If we have food but its not ideal for pet, give it to a
                # magic pet which will eat anything.
                if not mouth:
                    mouth = find_pet_to_feed(magic_pets, items, suffix, False)

                if mouth:
                    before = pets[mouth]

                    # if the less than ideal food is fed to a pet it's satiety
                    # increases by 1 not 5, so find the multiple of five.
                    satiety = int(5 * round(pets[mouth]/5))
                    # 50 is "fully fed and now a mount", 5 is best food growth
                    need_bites = bites = (50 - satiety) / 5
                    if items['food'][food] < bites:
                        bites = items['food'][food]

                    # Report how many more bites are needed before a mount.
                    moar = ""
                    if need_bites > bites:
                        need_bites -= bites
                        moar = " (needs %d more serving%s)" % (need_bites,
                                "" if need_bites == 1 else "s")

                    fed_foods.add(food)
                    print("Feeding %d %s to %s%s" % (bites, nice_name(food),
                                                   nice_name(mouth), moar))
                    before_user = user
                    feeder = api.Habitica(auth=auth, resource="user", aspect="feed")
                    for i in range(int(bites)):
                        feeder(_method='post', _one=mouth, _two=food)
                    user = hbt.user()
                    show_delta(hbt, before_user, user)
                    refreshed = True
                    items = user.get('items', [])
                    pets = items['pets']
                    if pets[mouth] == before:
                        raise ValueError("failed to feed %s" % (mouth))
                    break

        for food in list(attempted_foods - fed_foods):
            print("Nobody wants to eat %i %s" % (items['food'][food], nice_name(food)))

    # Hatch all possible eggs (v3 ok)
    elif args['<command>'] == 'hatch':
        def hatch_refresh(user):
            items = user.get('items', [])
            pets = items['pets']
            mounts = items['mounts']
            eggs = items['eggs']
            potions = items['hatchingPotions']
            return (items, pets, mounts, eggs, potions)

        user = hbt.user()
        refreshed = True

        while refreshed:
            refreshed = False
            items, pets, mounts, eggs, potions = hatch_refresh(user)

            for egg in eggs:
                # Skip eggs we don't have.
                if eggs[egg] == 0:
                    continue

                creatures = []
                for kind in kinds:
                    creatures.append('%s-%s' % (egg, kind))

                for creature in creatures:
                    # This pet is already hatched.
                    if pets.get(creature, 0) > 0:
                        continue

                    # We ran out of eggs.
                    if eggs[egg] == 0:
                        continue

                    potion = creature.split('-')[-1]
                    # Missing the potion needed for this creature.
                    if potion not in potions or potions[potion] < 1:
                        print("Want to hatch a %s %s, but missing potion" %
                              (potion, egg))
                        continue

                    print("Hatching a %s %s" % (nice_name(potion),
                                                nice_name(egg)))
                    before_user = user
                    hatcher = api.Habitica(auth=auth, resource="user", aspect="hatch")
                    hatcher(_method='post', _one=egg, _two=potion)
                    user = hbt.user()
                    show_delta(hbt, before_user, user)
                    refreshed = True
                    items, pets, mounts, eggs, potions = hatch_refresh(user)
                    if pets.get(creature, 0) != 5:
                        raise ValueError("failed to hatch %s" % (creature))

        # How many eggs do we need for the future?
        tosell = []
        for egg in eggs:
            need_pets = []
            need_mounts = []

            # Don't bother reporting about eggs we have none of.
            if eggs[egg] == 0:
                continue

            creatures = []
            for kind in kinds:
                creatures.append('%s-%s' % (egg, kind))

            for creature in creatures:
                if mounts.get(creature, 0) == 0:
                    name = nice_name(creature.split('-',1)[1])
                    need_mounts.append(name)
                if pets.get(creature, 0) < 5:
                    need_pets.append(creature.split('-',1)[1])

            report = ""
            if len(need_pets):
                report += "%d Pet%s (%s)" % (len(need_pets),
                          "" if len(need_pets) == 1 else "s",
                          ", ".join(need_pets))
            if len(need_mounts):
                if len(report):
                    report += ", "
                report += "%d Mount%s (%s)" % (len(need_mounts),
                          "" if len(need_mounts) == 1 else "s",
                          ", ".join(need_mounts))
            if settings['eggs-extra']:
                if len(report):
                    report += ", "
                report += "%d extra" % (settings['eggs-extra'])

            need = len(need_pets) + len(need_mounts) + settings['eggs-extra']
            if need and need != settings['eggs-extra']:
                print("%s egg: Need %d for %s" % (nice_name(egg), need, report))

            # Sell unneeded eggs.
            sell = eggs[egg] - need
            if sell > 0:
                before = eggs[egg]
                print("Selling %d %s egg%s" % (sell, nice_name(egg),
                                               "" if sell == 1 else "s"))
                for i in range(sell):
                    tosell.append(egg)

        if len(tosell) > 0:
            before_user = user
            seller = api.Habitica(auth=auth, resource="user", aspect="sell")
            for i in range(len(tosell)):
                seller(_method='post', _one='eggs', _two=tosell[i])
            user = hbt.user()
            show_delta(hbt, before_user, user)

    # Sell all unneeded hatching potions (v3 ok)
    elif args['<command>'] == 'sell':
        sell_reserved = settings['sell-reserved']
        sell_max = settings['sell-max']
        if "max" in args['<args>']:
            arg = args['<args>'].index("max")
            name = args['<args>'].pop(arg)
            sell_max = int(args['<args>'].pop(arg))

        user = hbt.user()

        selling = args['<args>']
        if len(selling) == 0:
            do_item_enumerate(user, ['hatchingPotions'], ordered=True)
            sys.exit(0)

        if selling == ['all']:
            selling = kinds

        tosell = []
        items = user.get('items', [])
        stats = user.get('stats', [])
        potions = items['hatchingPotions']
        for sell in selling:
            if sell not in kinds:
                print("\"%s\" isn't a valid kind of potion." % (sell))
                sys.exit(1)
            if sell not in potions:
                print("You don't have any \"%s\"." % (sell))
                continue

            # Only sell potions above "sell-reserved" setting.
            if sell_reserved != -1:
                if potions[sell] < sell_reserved:
                    continue
                potions[sell] -= sell_reserved
            # Don't sell more than "sell-max" setting.
            if sell_max != -1 and potions[sell] > sell_max:
                potions[sell] = sell_max

            # Sell potions!
            if potions[sell] > 0:
                print("Selling %d %s potion%s" % (potions[sell],
                        nice_name(sell),
                        "" if potions[sell] == 1 else "s"))
                for i in range(potions[sell]):
                    tosell.append(sell)
        if len(tosell):
            before_user = user
            seller = api.Habitica(auth=auth, resource="user", aspect="sell")
            for i in range(len(tosell)):
                seller(_method='post', _one='hatchingPotions', _two=tosell[i])
            user = hbt.user()
            show_delta(hbt, before_user, user)

    # dump raw json for user (v3 ok)
    elif args['<command>'] == 'dump':
        user = None
        party = None
        items = None
        report = {}
        wanted = args['<args>']
        if len(wanted) == 0:
            wanted = ['user', 'party', 'members']

        # Fetch stuff we need for multiple targets.
        if 'user' in wanted or 'food' in wanted or 'pets' in wanted or 'mounts' in wanted:
            user = hbt.user()
        if 'food' in wanted or 'pets' in wanted or 'mounts' in wanted:
            items = user.get('items', [])
        if 'party' in wanted or 'members' in wanted:
            party = hbt.groups.party()

        # Add report details.
        if 'user' in wanted:
            report['user'] = user
        if 'party' in wanted:
            report['party'] = party
        if 'members' in wanted:
            group = api.Habitica(auth=auth, resource="groups", aspect=party['id'])
            report['members'] = group(_one='members')
        if 'food' in wanted:
            report['food'] = items['food']
        if 'pets' in wanted:
            report['pets'] = items['pets']
        if 'mounts' in wanted:
            report['mounts'] = items['mounts']
        if 'content' in wanted:
            report['content'] = hbt.content()

        # Dump the report.
        print(json.dumps(report, indent=4, sort_keys=True))

    # cast/skill on task/self/party (v3 ok)
    elif args['<command>'] == 'cast':
        user = hbt.user()
        stats = user.get('stats', '')
        uclass = stats['class']

        # class: {spell: target}
        spells = {'warrior': {'valorousPresence': 'party',
                              'defensiveStance': 'self',
                              'smash': 'task',
                              'intimidate': 'party'},
                  'rogue': {'pickPocket': 'task',
                            'backStab': 'task',
                            'toolsOfTrade': 'party',
                            'stealth': 'self'},
                  'wizard': {'fireball': 'task',
                             'mpheal': 'party',
                             'earth': 'party',
                             'frost': 'self'
                            },
                  'healer': {'heal': 'self',
                             'healAll': 'party',
                             'protectAura': 'party',
                             'brightness': 'self'
                            }
                 }

        smart = {'heal': hp_down_ten,
                 'healAll': party_hp_down_ten,
                }

        if len(args['<args>']) == 0:
            for spell in spells[uclass]:
                print("%s (%s)" % (spell, spells[uclass][spell]))
            sys.exit(0)

        spell = args['<args>'][0]

        precast = None
        if spell == "smart":
            spell = args['<args>'].pop(1)
            if spell not in smart:
                print("There's no smart way to cast that.")
                sys.exit(1)
            precast = smart[spell]

        if len(args['<args>']) == 2:
            task = args['<args>'][1]
        else:
            task = ''

        if spell not in spells[uclass]:
            print("That isn't a spell you know.")
            sys.exit(1)
        target = spells[uclass][spell]
        if target == 'task' and not task:
            print("You need to provide a task id to target.")
            sys.exit(1)

        # Do some smart checks before casting?
        if precast != None:
            precast(auth, hbt, user)

        # Report casting.
        msg = "Casting %s" % (spell)
        if target == 'party':
            msg += " on the party"
        elif target == 'task':
            msg += " on task %s" % (task)
        msg += "."
        print(msg)

        before_user = user
        charclass = api.Habitica(auth=auth, resource="user", aspect="class")
        if task != '':
            charclass(_method='post', _one='cast', _two=spell, targetId=task)
        else:
            charclass(_method='post', _one='cast', _two=spell)
        user = hbt.user()
        show_delta(hbt, before_user, user)

    # buy as many gems as possible (v3 ok)
    elif args['<command>'] == 'gems':
        user = hbt.user()
        before_user = user
        # base of 25 + (5 * (months subscribed / 3)) which seems to be
        # gemCapExtra
        # c.f. http://habitica.wikia.com/wiki/Gems
        gem_buy_limit = 25 + int(user['purchased']['plan']['consecutive']['gemCapExtra'])
        gems = gem_buy_limit - int(user['purchased']['plan']['gemsBought'])

        purchaser = api.Habitica(auth=auth, resource="user", aspect="purchase")
        for i in range(gems):
            purchaser(_method='post', _one='gems', _two='gem')
        user = hbt.user()
        show_delta(hbt, before_user, user)

    elif args['<command>'] == 'armoire':
        user = hbt.user()
        before_user = user
        purchase = api.Habitica(auth=auth, resource="user",
                                aspect="buy-armoire")
        received = purchase(_method='post')
        print('Got ' + received['armoire']['dropText'] + '!')

    #Quest manipulations
    elif args['<command>'] == 'quest':
        # if on a quest with the party, grab quest info
        user = hbt.user()
        group = hbt.groups(type='party')
        party_id = group[0]['id']
        quest_data = getattr(hbt.groups, party_id)()['quest']
        if quest_data:
            quest_key = quest_data['key']

            if cache.get(SECTION_CACHE_QUEST, 'quest_key') != quest_key:
                # we're on a new quest, update quest key
                logging.info('Updating quest information...')
                content = hbt.content()
                quest_type = ''
                quest_max = '-1'
                quest_title = content['quests'][quest_key]['text']

                # if there's a content/quests/<quest_key/collect,
                # then drill into .../collect/<whatever>/count and
                # .../collect/<whatever>/text and get those values
                if content.get('quests', {}).get(quest_key,
                                                 {}).get('collect'):
                    logging.debug("\tOn a collection type of quest")
                    qt = 'collect'
                    clct = list(content['quests'][quest_key][qt].values())[0]
                    quest_max = clct['count']
                # else if it's a boss, then hit up
                # content/quests/<quest_key>/boss/hp
                elif content.get('quests', {}).get(quest_key,
                                                   {}).get('boss'):
                    logging.debug("\tOn a boss/hp type of quest")
                    qt = 'hp'
                    quest_max = content['quests'][quest_key]['boss'][qt]

                # store repr of quest info from /content
                cache = update_quest_cache(CACHE_CONF,
                                           quest_key=str(quest_key),
                                           quest_type=str(qt),
                                           quest_max=str(quest_max),
                                           quest_title=str(quest_title))

            # now we use /party and quest_type to figure out our progress!
            quest_type = cache.get(SECTION_CACHE_QUEST, 'quest_type')
            if quest_type == 'collect' and quest_data['active']:
                qp_tmp = quest_data['progress']['collect']
                if type(qp_tmp) is not dict:
                    quest_progress = qp_tmp.values()[0]
                else:
                    quest_progress = list(qp_tmp.values())[0]
            elif quest_data['active']:
                quest_progress = quest_data['progress']['hp']
            else:
                quest_progress = cache.get(SECTION_CACHE_QUEST, 'quest_max')

            if quest_data['active']:
                quest = '"%s" - %s/%s (-%s)' % (
                        cache.get(SECTION_CACHE_QUEST, 'quest_title'),
                        str(int(quest_progress)),
                        cache.get(SECTION_CACHE_QUEST, 'quest_max'),
                        str(int(user['party']['quest']['progress']['up'])))
                            
            else:
                quest = '%s "%s"' % (
                            'Preparing',
                            cache.get(SECTION_CACHE_QUEST, 'quest_title'))

            groupUserStatus = group_user_status(quest_data, auth, hbt)

            len_ljust = 6
            print('%s %s' % ('Quest:'.rjust(len_ljust, ' '), quest))
            print_gus(groupUserStatus, len_ljust)


    # Select a pet or mount (v3 ok)
    elif args['<command>'] == 'ride' or args['<command>'] == 'walk':
        if args['<command>'] == 'ride':
            item_type = 'mounts'
            current = 'currentMount'
            name = 'mount'
            verb = 'riding'
        else:
            item_type = 'pets'
            current = 'currentPet'
            name = 'pet'
            verb = 'walking with'

        user = hbt.user()
        items = user.get('items', [])
        animals = items[item_type]

        if len(args['<args>']) == 0:
            do_item_enumerate(user, [item_type], ordered=True, pretty=False)
            return

        desired = "".join(args['<args>'])

        if desired.startswith('rand'):
            active = items.get(current, '')
            if active and len(animals) > 1:
                animals.pop(active)

            choice = random.randrange(0, len(animals)-1)
            chosen = animals.keys()[choice]
        else:
            if desired not in animals:
                print("You don't have a '%s' %s!" % (desired, name))
                sys.exit(1)
            chosen = desired

        equiper = batch = api.Habitica(auth=auth, resource="user", aspect="equip")
        equiper(_method='post', _one=name, _two=chosen)
        print("You are now %s a %s" % (verb, nice_name(chosen)))

    # equip a set of equipment (v3 ok)
    elif args['<command>'] == 'equip':
        equipping = args['<args>']
        user = hbt.user()
        before_user = user
        items = user.get('items', [])
        equipped = items['gear']['equipped']

        equiper = batch = api.Habitica(auth=auth, resource="user", aspect="equip")
        for equipment in equipping:
            equiper(_method='post', _one='equipped', _two=equipment)
        user = hbt.user()
        show_delta(hbt, before_user, user)

    # sleep/wake up (v3 ok)
    elif args['<command>'] == 'sleep' or args['<command>'] == 'arise':
        user = hbt.user()
        intent = args['<command>']
        sleeping = user['preferences']['sleep']
        if intent == 'sleep' and sleeping:
            print("You are already resting.")
            sys.exit(1)
        if not sleeping and intent == 'arise':
            print("You are already checked out.")
            sys.exit(1)

        sleeper = api.Habitica(auth=auth, resource="user", aspect="sleep")
        sleeper(_method='post')

    # GET user status (v3 ok)
    elif args['<command>'] == 'status':

        # gather status info
        user = hbt.user()
        guilds = user.get('guilds')
        party = hbt.groups.party()
        stats = user.get('stats', '')
        group = hbt.groups(type='party')
        items = user.get('items', '')
        sleeping = user['preferences']['sleep']
        food_count = sum(items['food'].values())
        newMessages = user.get('newMessages', '')
        # gather quest progress information (yes, janky. the API
        # doesn't make this stat particularly easy to grab...).
        # because hitting /content downloads a crapload of stuff, we
        # cache info about the current quest in cache.
        quest = 'Not currently on a quest'
        if (party is not None and
                party.get('quest', '')): 

            quest_key = party['quest']['key']

            if cache.get(SECTION_CACHE_QUEST, 'quest_key') != quest_key:
                # we're on a new quest, update quest key
                logging.info('Updating quest information...')
                content = hbt.content()
                quest_type = ''
                quest_max = '-1'
                quest_title = content['quests'][quest_key]['text']

                # if there's a content/quests/<quest_key/collect,
                # then drill into .../collect/<whatever>/count and
                # .../collect/<whatever>/text and get those values
                if content.get('quests', {}).get(quest_key, {}).get('collect'):
                    logging.debug("\tOn a collection type of quest")
                    quest_type = 'collect'
                    clct = content['quests'][quest_key]['collect'].values()[0]
                    quest_max = clct['count']
                # else if it's a boss, then hit up
                # content/quests/<quest_key>/boss/hp
                elif content.get('quests', {}).get(quest_key, {}).get('boss'):
                    logging.debug("\tOn a boss/hp type of quest")
                    quest_type = 'hp'
                    quest_max = content['quests'][quest_key]['boss']['hp']

                # store repr of quest info from /content
                cache = update_quest_cache(CACHE_CONF,
                                           quest_key=str(quest_key),
                                           quest_type=str(quest_type),
                                           quest_max=str(quest_max),
                                           quest_title=str(quest_title))

            # now we use /party and quest_type to figure out our progress!
            quest_type = cache.get(SECTION_CACHE_QUEST, 'quest_type')
            if quest_type == 'collect' and party['quest']['active']:
                qp_tmp = party['quest']['progress']['collect']
                if type(qp_tmp) is not dict:
                    quest_progress = qp_tmp.values()[0]
                else:
                    quest_progress = list(qp_tmp.values())[0]
            elif party['quest']['active']:
                quest_progress = party['quest']['progress']['hp']
            else:
                quest_progress = cache.get(SECTION_CACHE_QUEST, 'quest_max')

            if party['quest']['active']:
                quest = '"%s" - %s/%s (-%s)' % (
                            cache.get(SECTION_CACHE_QUEST, 'quest_title'),
                            str(int(quest_progress)),
                            cache.get(SECTION_CACHE_QUEST, 'quest_max'),
                            str(int(user['party']['quest']['progress']['up'])))
                            
            else:
                quest = '%s "%s"' % (
                            'Preparing',
                            cache.get(SECTION_CACHE_QUEST, 'quest_title'))


        egg_count = sum(items['eggs'].values())
        potion_count = sum(items['hatchingPotions'].values())

        # prepare and print status strings
        title = user['profile']['name']
        title += ' - Level %d %s' % (stats['lvl'], stats['class'].capitalize())
        if sleeping:
            title += ' (zZZz)'
        health = '%d/%d' % (stats['hp'], stats['maxHealth'])
        xp = '%d/%d' % (int(stats['exp']), stats['toNextLevel'])
        mana = '%d/%d' % (int(stats['mp']), stats['maxMP'])
        currency = get_currency(stats.get('gp', 0), user.get('balance', "0"))
        currentPet = items.get('currentPet', '')
        if not currentPet:
            currentPet = DEFAULT_PET
        pet = '%s (%d food items)' % (currentPet, food_count)
        pet = '%s' % (currentPet)
        perishables = '%d serving%s, %d egg%s, %d potion%s' % \
                      (food_count, "" if food_count == 1 else "s",
                       egg_count, "" if egg_count == 1 else "s",
                       potion_count,  "" if potion_count == 1 else "s")
        mount = items.get('currentMount', '')
        if not mount:
            mount = DEFAULT_MOUNT

        members = get_members(auth, party)
        summary_items = ('health', 'xp', 'mana', 'currency', 'perishables',
                         'quest', 'pet', 'mount', 'group')
        len_ljust = max(map(len, summary_items)) + 1

        groupUserStatus = {}
        groupUserStatus['users'] = {}
        for member in members:
            user = member['profile']['name']
            groupUserStatus['users'][user] = {}
            groupUserStatus.setdefault('longestname', 1)
            if len(member['profile']['name']) > groupUserStatus['longestname']:
                    groupUserStatus['longestname'] = len(member['profile']['name'])
            groupUserStatus['users'][user]['name'] = member['profile']['name']
            if member['preferences']['sleep']:
                    groupUserStatus['users'][user]['sleep'] = 'sleeping'
            else:
                    groupUserStatus['users'][user]['sleep'] = 'active'
            groupUserStatus['users'][user]['lastactive'] = member['auth']['timestamps']['loggedin']
            stats = ['hp', 'maxHealth', 'mp', 'maxMP', 'class']
            for stat in stats:
                groupUserStatus['users'][user][stat] = member['stats'][stat]
            
        groupUserStatus['users'] = OrderedDict(sorted(groupUserStatus['users'].items(), key=lambda t: t[1]['lastactive']))

        messages = 'No new messages.'
        if newMessages:
            messages = 'New messages in '
            for gid, message in newMessages.items():
                if gid != party['id']:
                    messages = messages + message['name'] + '(' + str(guilds.index(gid)+1) + '), '
                else:
                    messages = messages + message['name'] + '(0), '
            messages = messages[:-2] + '!'

        print('=' * len(title))
        print(title)
        print('=' * len(title))
        print(textwrap.fill(messages, width=80))
        print('-' * min(max(len(messages), len(title)), 80))
        print('%s %s' % ('Health:'.rjust(len_ljust, ' '), health))
        print('%s %s' % ('XP:'.rjust(len_ljust, ' '), xp))
        print('%s %s' % ('Mana:'.rjust(len_ljust, ' '), mana))
        print('%s %s' % ('Currency:'.rjust(len_ljust, ' '), currency))
        print('%s %s' % ('Perishables:'.rjust(len_ljust, ' '), perishables))
        print('%s %s' % ('Pet:'.rjust(len_ljust, ' '), nice_name(pet)))
        print('%s %s' % ('Mount:'.rjust(len_ljust, ' '), nice_name(mount)))
        print('%s %s' % ('Quest:'.rjust(len_ljust, ' '), quest))
        print('%s %s' % ('Group:'.rjust(len_ljust, ' '), group[0]['name']))

        len_ljust += 1
        headLine = ''.rjust(len_ljust, ' ')
        headLine += 'Name'.ljust(groupUserStatus['longestname'] + 1)
        headLine += 'Class'.ljust(9, ' ')
        headLine += 'Status'.ljust(10, ' ')
        headLine += 'Last login'.ljust(15, ' ')
        headLine += 'Health'.ljust(8, ' ')
        headLine += 'Mana'.ljust(8, ' ')
        print(headLine)

        print(' '.rjust(len_ljust, ' ') + '-' * (len(headLine) - len_ljust))

        for user in groupUserStatus['users'].values():
            userLine = ' '.rjust(len_ljust, ' ')
            userLine += user['name'].ljust(groupUserStatus['longestname'] + 1)
            userLine += user['class'].capitalize().ljust(9, ' ') 
            userLine += user['sleep'].ljust(10, ' ')
            userLine += humanize.naturaltime(datetime.datetime.now(pytz.utc) - dateutil.parser.parse(user['lastactive'])).ljust(15, ' ')
            userLine += (str(int(user['hp'])) + '/' + str(user['maxHealth'])).ljust(8, ' ')
            userLine += (str(int(user['mp'])) + '/' + str(user['maxMP'])).ljust(8, ' ')
            print(userLine)



    # GET/POST habits (v3 ok)
    elif args['<command>'] == 'habits':
        habits = hbt.tasks.user(type='habits')
        direction = None
        if 'up' in args['<args>']:
            report = 'incremented'
            direction = 'up'
        elif 'down' in args['<args>']:
            report = 'decremented'
            direction = 'down'

        if direction != None:
            before_user = hbt.user()
            tids = get_task_ids(args['<args>'][1:])
            for tid in tids:
                tval = habits[tid]['value']
                habit = api.Habitica(auth=auth, resource="tasks", aspect=habits[tid]['id'])
                habit(_method='post', _one='score', _two=direction)
                print('%s habit \'%s\''
                      % (report, habits[tid]['text'])) #.encode('utf8')))
                if direction == 'up':
                    habits[tid]['value'] = tval + (TASK_VALUE_BASE ** tval)
                else:
                    habits[tid]['value'] = tval - (TASK_VALUE_BASE ** tval)
                #sleep(HABITICA_REQUEST_WAIT_TIME)
            show_delta(hbt, before_user, hbt.user())

        for i, task in enumerate(habits):
            score = qualitative_task_score_from_value(task['value'])
            print('[%s] %s %s' % (score, i + 1, task['text'])) #.encode('utf8')))

    # GET/PUT tasks:daily (v3 ok)
    elif args['<command>'] == 'dailies':
        dailies = hbt.tasks.user(type='dailys')
        direction = None
        if 'done' in args['<args>']:
            report = 'completed'
            direction = 'up'
        elif 'undo' in args['<args>']:
            report = 'incomplete'
            direction = 'down'

        if direction != None:
            before_user = hbt.user()
#            tids = get_task_ids(args['<args>'][1:])
            tids = args['<args>'][1:]  
            for tid in tids:
                checklistItem = isChecklistItem(tid)
                if checklistItem == False:
                    tid = int(tid) - 1
                    daily = api.Habitica(auth=auth, resource="tasks", aspect=dailies[tid]['id'])
                    daily(_method='post', _one='score', _two=direction)
                    print('marked daily \'%s\' %s'
                          % (dailies[tid]['text'], report)) #.encode('utf8'))) - for the first string
                    if direction == 'up':
                        dailies[tid]['completed'] = True
                    else:
                        dailies[tid]['completed'] = False
                    #sleep(HABITICA_REQUEST_WAIT_TIME)
                elif checklistItem == None:
                    print('Could not parse argument \'%s\' - ignoring it!' % tid)
                else:
                    checklist = api.Habitica(auth=auth, resource="tasks", 
                                             aspect=dailies[checklistItem[0]]['id'])
                    print('toggled checklist item \'%s\' of daily \'%s\''
                          % (dailies[checklistItem[0]]['checklist'][checklistItem[1]]['text'],
                             dailies[checklistItem[0]]['text']))
                    checklist(_method='post', _one='checklist',
                        _two=dailies[checklistItem[0]]['checklist'][checklistItem[1]]['id'] + '/score')
                    dailies[checklistItem[0]]['checklist'][checklistItem[1]]['completed'] = \
                        not dailies[checklistItem[0]]['checklist'][checklistItem[1]]['completed']
            show_delta(hbt, before_user, hbt.user())

        print_task_list(dailies)

    # handle todo items (v3 ok)
    elif args['<command>'] == 'todos':
        todos = [e for e in hbt.tasks.user(type='todos')
                 if not e['completed']]
        if 'done' in args['<args>']:
            before_user = hbt.user()
#            tids = get_task_ids(args['<args>'][1:])
            tids = args['<args>'][1:]
            for tid in tids:
                checklistItem = isChecklistItem(tid)
                if checklistItem == False:
                    todo = api.Habitica(auth=auth, resource="tasks", aspect=todos[tid]['id'])
                    todo(_method='post', _one='score', _two='up')
                    print('marked todo \'%s\' complete'
                          % todos[tid]['text']) #.encode('utf8'))
                    #sleep(HABITICA_REQUEST_WAIT_TIME)
                    todos = updated_task_list(todos, tids)
                elif checklistItem == None:
                    print('Could not parse argument \'%s\' - ignoring it!' % tid)
                else:
                    checklist = api.Habitica(auth=auth, resource="tasks",
                                             aspect=todos[checklistItem[0]]['id'])
                    print('toggled checklist item \'%s\' of daily \'%s\''
                          % (todos[checklistItem[0]]['checklist'][checklistItem[1]]['text'],
                             todos[checklistItem[0]]['text']))
                    checklist(_method='post', _one='checklist',
                        _two=todos[checklistItem[0]]['checklist'][checklistItem[1]]['id'] + '/score')
                    todos[checklistItem[0]]['checklist'][checklistItem[1]]['completed'] = \
                        not todos[checklistItem[0]]['checklist'][checklistItem[1]]['completed']
            show_delta(hbt, before_user, hbt.user())
        elif 'get' in args['<args>']:
            tids = get_task_ids(args['<args>'][1:])
            for tid in tids:
                todo = api.Habitica(auth=auth, resource="tasks", aspect=todos[tid]['id'])
                obj = todo(_method='get')
                print(json.dumps({'todo':obj}, indent=4, sort_keys=True))
        elif 'add' in args['<args>']:
            ttext = ' '.join(args['<args>'][1:])
            hbt.tasks.user(type='todo',
                           text=ttext,
                           priority=PRIORITY[args['--difficulty']],
                           _method='post')
            todos.insert(0, {'completed': False, 'text': ttext})
            print('added new todo \'%s\'' % ttext)
        elif 'delete' in args['<args>']:
            tids = get_task_ids(args['<args>'][1:])
            for tid in tids:
                hbt.user.tasks(_id=todos[tid]['id'],
                               _method='delete')
                print('deleted todo \'%s\''
                      % todos[tid]['text'])
                sleep(HABITICA_REQUEST_WAIT_TIME)
            todos = updated_task_list(todos, tids)
        print_task_list(todos)

    elif args['<command>'] == 'chat':           
        user = hbt.user()
        guilds = user.get('guilds')
        
        if args['<args>'][0] == 'list':
            print('0 %s' % hbt.groups.party()['name'])
            if 'timestamp' in cache['Guildnames'].keys() and \
             time() - float(cache['Guildnames']['timestamp']) < 604800:
                for i in range(len(guilds)):
                    try:
                        name = cache.get(SECTION_CACHE_GUILDNAMES, guilds[i])
                    except configparser.NoOptionError:
                        name = getattr(hbt.groups, guilds[i])()['name']
                        cache = update_guildnames_cache(CACHE_CONF,
                                               number=guilds[i],
                                               name=name)
                    print('%d %s' % (i + 1, name))

            else:
                cache = update_guildnames_cache(CACHE_CONF,
                                          number='timestamp',
                                          name=str(time()))
                for i in range(len(guilds)):
                    name = getattr(hbt.groups, guilds[i])()['name']
                    cache = update_guildnames_cache(CACHE_CONF,
                                               number=guilds[i],
                                               name=name)
                    print('%d %s' % (i + 1, name))
        
        elif args['<args>'][0] == 'show':
            messageNum = 5
            if len(args['<args>']) > 3 or len(args['<args>']) < 0: 
                print('Invalid number of arguments! Must be group number '
                      '+ (optional) number of messages to show.')
                sys.exit(1)
            elif len(args['<args>']) == 1:
                party = user.get('party')['_id'] 
            elif len(args['<args>']) == 2:
                party = chatID(args['<args>'][1], user, guilds)
            else:
                try:
                    messageNum = int(args['<args>'][2])
                except ValueError:
                    print('Number of messages must be a number!')
                    sys.exit(1)
                party = chatID(args['<args>'][1], user, guilds)

            chat = api.Habitica(auth=auth, resource="groups", aspect=party)
            messages = chat(_one='chat')
            chat(_method='post', _one='chat', _two='seen')
            printChatMessages(messages, messageNum)

        elif args['<args>'][0] == 'send':
            party = chatID(args['<args>'][1], user, guilds)
            chat = api.Habitica(auth=auth, resource="groups", aspect=party)
            send = chat(message=args['<args>'][2:], _method='post', _one='chat')

            messages = chat(_one='chat')
            printChatMessages(messages, 5)
            chat(_method='post', _one='chat', _two='seen')


    else:
        print("Unknown command '%s'" % (args['<command>']))
        sys.exit(1)


if __name__ == '__main__':
    cli()
