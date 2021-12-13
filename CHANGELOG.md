
1.2.0.0 (December 12, 2021)

* Early support for GHC 9.2.1 (thanks to Alan Zimmerman) 
* Dropped support for GHC <9.2 (might readd it later)

1.1.0.0 (November 13, 2021)
* Remove dependency on xargs (#31)
* Allow rewrite elaboration

1.0.0.0 (April 9, 2021)

* Added --adhoc-type flag (#13)
* Added --adhoc-pattern, --pattern-forward, --pattern-backward (#15)
* Speed up file search when large number of files match.
* Removed support for GHC 8.4 and 8.8
* Added support for GHC 9.0.1

0.1.1.1 (June 1, 2020)

* Remove dependency on haskell-src-exts from library (#9)
* Support additional pattern syntax when generating fold/unfold rewrites (#8)
* Limit partial-application rewrite variants to irrefutible patterns (#7)
* Fix handling of qualified names during substitution (#5)
* Fix self-recursion check for do-syntax binds (#5)
* Fix bug in grep invocation for relative target paths (#5)

0.1.1.0 (May 8, 2020)

* Support GHC 8.10.1

0.1.0.1 (April 1, 2020)

* Don't fail if 'git' or 'hg' commands cannot be found.
* Better error message when syntax support needs to be extended.
* Add support for following type syntax: lists, tuples, constraints,
  unboxed sums, and forall.

0.1.0.0 (March 16, 2020)

Initial release
