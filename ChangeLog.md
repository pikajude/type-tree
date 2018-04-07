# Revision history for type-tree

## 0.2.0.1 -- 2018-04-07

* `liftName` no longer produces invalid code if passed a NameU (i.e. the result of
  `newName`).

## 0.2.0.0 -- 2018-04-07

* Moved from Tree to Forest representation of types
* Type variable resolution has been removed as it's unneeded
* Cycle detection is now a lot more straightforward

## 0.1.0.1 -- 2018-03-29

* Fixing a minor documentation typo

## 0.1.0.0 -- 2018-03-27

* Initial release
