#!/bin/sh

sed -e 's/((const char\*)((char\*)(& \([a-z]*\))))/\1/g'
