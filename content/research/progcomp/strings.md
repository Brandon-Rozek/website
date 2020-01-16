# Strings

## Character Codes

Character codes are mappings between numbers and symbols which make up a particular alphabet.

The *American Standard Code for Information Interchange* (ASCII) is a single-byte character code where $2^7 = 128$ characters are specified.

Symbol assignments were not done at random. Several interesting properties of the design make programming tasks easier:

- All non-printable characters have either the first three bits as zero or all seven lowest bits as one. This makes it easy to eliminate them before displaying junk.
- Both the upper and lower case letters and the numerical digits appear sequentially
- We can get the numeric order of a letter by subtracting the first letter
- We can convert a character from uppercase to lowercase by $Letter - "A" + "a"$ 

