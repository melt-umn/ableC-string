String extension
================

This extension provides a wrapper around char* strings, providing a number of useful operators.  
The purpose of this extension is to provide a simple demo of operator overloading.  

Operators include
* String append: `s1 + s2`
* String repeat: `s * i`
* String equality: `s1 == s2`
* String index: `s[i]`
* String coercion operator: `str(x)`
* String representation operator: `show(x)`
* Compute the size of buffer needed to be allocated to show a value: `showMaxLen(x)`
* Show a value to a buffer: `showToBuf(buf, x)`
* Write a string construction expression to a buffer without allocating: `buildStr(buf, x + "foo" + y)`
