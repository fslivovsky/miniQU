#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Mar 24 15:22:44 2022

@author: fs
"""
import sys

from trace_parser import TraceParser

if __name__ == "__main__":
  filename_in = sys.argv[1]
  filename_out = sys.argv[2]
  t = TraceParser(filename_in)
  t.toQRP(filename_out)