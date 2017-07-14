#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
Phil Adams http://philadams.net

Python wrapper around the Habitica (http://habitica.com) API
http://github.com/philadams/habitica
"""


import json

import requests

API_URI_BASE = 'api/v3'
API_CONTENT_TYPE = 'application/json'


class Habitica(object):
    """
    A minimalist Habitica API class.
    """

    def __init__(self, auth=None, resource=None, aspect=None):
        self.auth = auth
        self.resource = resource
        self.aspect = aspect
        self.headers = auth if auth else {}
        self.headers.update({'content-type': API_CONTENT_TYPE})

    def __getattr__(self, m):
        try:
            return object.__getattr__(self, m)
        except AttributeError:
            if not self.resource:
                return Habitica(auth=self.auth, resource=m)
            else:
                return Habitica(auth=self.auth, resource=self.resource,
                                aspect=m)

    def __call__(self, **kwargs):
        method = kwargs.pop('_method', 'get')

        # build up URL... Habitica's api is the *teeniest* bit annoying
        # so either i need to find a cleaner way here, or i should
        # get involved in the API itself and... help it.
        if self.aspect:
            aspect_id = kwargs.pop('_id', None)
            direction = kwargs.pop('_direction', None)
            if aspect_id is not None:
                uri = '%s/%s/%s/%s/%s' % (self.auth['url'],
                                          API_URI_BASE,
                                          self.resource,
                                          self.aspect,
                                          str(aspect_id))
            arg_one = kwargs.pop('_one', None)
            arg_two = kwargs.pop('_two', None)
            uri = '%s/%s' % (self.auth['url'], API_URI_BASE)
            if arg_one is not None:
                uri += '/%s/%s/%s' % (self.resource, self.aspect,
                                      str(arg_one))
            else:
                uri = '%s/%s/%s/%s' % (self.auth['url'],
                                       API_URI_BASE,
                                       self.resource,
                                       self.aspect)
            if direction is not None:
                uri = '%s/%s' % (uri, direction)
                uri += '/%s/%s' % (self.resource, self.aspect)
            if arg_two is not None:
                uri = '%s/%s' % (uri, arg_two)
        else:
            uri = '%s/%s/%s' % (self.auth['url'],
                                API_URI_BASE,
                                self.resource)
        #print(uri)
        # actually make the request of the API
        if method in ['put', 'post'] and self.aspect \
                not in ['class', 'inventory']:
            if not self.aspect == None and 'batch-update' in self.aspect:
                data = json.dumps(kwargs.pop('ops', []))
            else:
                data = json.dumps(kwargs)
            #print(data)
            res = getattr(requests, method)(uri, headers=self.headers,
                                            data=data)
        else:
            # from ipdb import set_trace; set_trace()
            res = getattr(requests, method)(uri, headers=self.headers,
                                            params=kwargs)

        # print(res.url)  # debug...
        if res.status_code == requests.codes.ok or requests.codes.created:
            if "data" in res.json():
                return res.json()["data"]
            else:
                return None
        else:
            print(res.url)
            res.raise_for_status()
