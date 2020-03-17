Retrie is a powerful, easy-to-use codemodding tool for Haskell. 

# Install

```
cabal update
cabal install retrie
```

# Example

Assume you have some code, including functions like `foo`:

```haskell
module MyModule where

foo :: [Int] -> [Int]
foo ints = map bar (map baz ints)
```

Someone points out that traversing the list `ints` twice is slower than doing it once. You could fix the code by hand, or you could rewrite it with retrie:

```bash
retrie --adhoc "forall f g xs. map f (map g xs) = map (f . g) xs"
```

Retrie applies the equation as a rewrite to all the Haskell modules it finds in the current directory:

```diff
 module MyModule where

 foo :: [Int] -> [Int]
-foo ints = map bar (map baz ints)
+foo ints = map (bar . baz) ints
```

Of course, now you might find this code more difficult to understand. You also learn that GHC will do this sort of optimization automatically, so you decide to undo your rewrite:

```bash
retrie --adhoc "forall f g xs. map (f . g) xs = map f (map g xs)"
```

Now you have your original code back.

# Other Sources Of Equations

* The `--adhoc` flag, above, admits anything you can specify in a `RULES` pragma.
* You can apply actual `RULES` pragmas, in either direction, with `--rule-forward` and `--rule-backward`.
* Since definitions in Haskell are themselves equations, you can unfold (or inline) function definitions with `--unfold`. You can also fold a function definition with `--fold`, replacing an instance of the function's body with a call to that function.
* Type synonyms are also equations. You can apply type synonyms in either direction using `--type-forward` and `--type-backward`.

To try some examples, put the following into `MyModule2.hs`:

```haskell
module MyModule2 where

maybe :: b -> (a -> b) -> Maybe a -> b
maybe d f mb = case mb of
  Nothing -> d
  Just x -> f x

type MyMaybe = Maybe Int

{-# RULES "myRule" forall x. maybe Nothing Just x = x #-}

foo :: Maybe Int
foo = maybe Nothing Just (Just 5)
```

Then try the following rewrites and check the contents of the module after each step:

```bash
retrie --type-backward MyModule2.MyMaybe
```

```diff
 module MyModule2 where

 maybe :: b -> (a -> b) -> Maybe a -> b
 maybe d f mb = case mb of
   Nothing -> d
   Just x -> f x

 type MyMaybe = Maybe Int

 {-# RULES "myRule" forall x. maybe Nothing Just x = x #-}

-foo :: Maybe Int
+foo :: MyMaybe
 foo = maybe Nothing Just (Just 5)
```

```bash
retrie --unfold MyModule2.maybe
```

```diff
 module MyModule2 where

 maybe :: b -> (a -> b) -> Maybe a -> b
 maybe d f mb = case mb of
   Nothing -> d
   Just x -> f x

 type MyMaybe = Maybe Int

-{-# RULES "myRule" forall x. maybe Nothing Just x = x #-}
+{-# RULES "myRule" forall x. case x of
+            Nothing -> Nothing
+            Just x1 -> Just x1 = x #-}

 foo :: MyMaybe
-foo = maybe Nothing Just (Just 5)
+foo = case Just 5 of
+  Nothing -> Nothing
+  Just x -> Just x
```

```bash
retrie --fold MyModule2.maybe
```

```diff
 module MyModule2 where

 maybe :: b -> (a -> b) -> Maybe a -> b
 maybe d f mb = case mb of
   Nothing -> d
   Just x -> f x

 type MyMaybe = Maybe Int

-{-# RULES "myRule" forall x. case x of
-            Nothing -> Nothing
-            Just x1 -> Just x1 = x #-}
+{-# RULES "myRule" forall x. maybe Nothing Just x = x #-}

 foo :: MyMaybe
-foo = case Just 5 of
-  Nothing -> Nothing
-  Just x -> Just x
+foo = maybe Nothing Just (Just 5)
```

```bash
retrie --rule-forward MyModule2.myRule
```

```diff
 module MyModule2 where

 maybe :: b -> (a -> b) -> Maybe a -> b
 maybe d f mb = case mb of
   Nothing -> d
   Just x -> f x

 type MyMaybe = Maybe Int

 {-# RULES "myRule" forall x. maybe Nothing Just x = x #-}

 foo :: MyMaybe
-foo = maybe Nothing Just (Just 5)
+foo = Just 5
```

```bash
retrie --type-forward MyModule2.MyMaybe
```

```diff
 module MyModule2 where

 maybe :: b -> (a -> b) -> Maybe a -> b
 maybe d f mb = case mb of
   Nothing -> d
   Just x -> f x

 type MyMaybe = Maybe Int

 {-# RULES "myRule" forall x. maybe Nothing Just x = x #-}

-foo :: MyMaybe
+foo :: Maybe Int
 foo = Just 5
```

# Motivation

Refactoring tools fall on a spectrum. At one end is simple string replacement (`grep` and `sed`). At the other is parsing an abstract-syntax tree (AST) and directly manipulating it. Broadly, the tradeoffs are:

* String manipulation
  * Hard to write: Essentially need to hand-roll a parser using a regular expression.
  * Limited power: Find and replace.
  * Fast.

* AST manipulation
  * Hard to write: Requires extensive domain knowledge about language/parser.
  * Very powerful.
  * Slow: Parsing and traversing large codebases is expensive.

Retrie finds a middle ground:

* Easy to write: Equations are defined using syntax of target language.
* Powerful:
  * Equations are more powerful than regular expressions.
  * Rewrites can be scripted and enforce side-conditions (see below).
* Fast: Search space is narrowed using `grep` before parsing. Time is (morally) proportional to the number of matches, not the number of target files.

# Features

* Power
  * Can rewrite expressions, types, and patterns.
  * Matching is up to alpha-equivalence.
  * Rewrites are equational: a quantifier that appears twice in the left-hand side must match the same expression (up to alpha-equivalence).
  * Inserts imports. (As specified by the user, and automatically in some cases.)
  * Rewrites can be scripted and have side conditions.
  * Uses GHC's parser, so supports all of the *de facto* Haskell language.
* Correctness
  * Local scoping is respected. (Will not introduce shadowing/capture bugs.)
  * Impossible to match/rewrite an incomplete expression fragment.
  * Parentheses are automatically removed/inserted as needed.
* Whitespace
  * Whitespace is ignored when matching. No fiddling with `\s`.
  * Whitespace is preserved in resulting expression.
* Will not rewrite in comments. Existing comments are preserved.
* Respects git/hg ignore files.

See `retrie --help` for a complete list of options.

# Scripting and Side Conditions

Retrie can be used as a library to tackle more complex rewrites.

Consider the task of changing the argument type of a function from `String` to an enumeration:

```haskell
fooOld :: String -> IO ()

data FooArg = Foo | Bar

fooNew :: FooArg -> IO ()
```

Retrie provides a small monadic DSL for scripting the application of rewrites. It also allows you to intercept and manipulate the result of matching the left-hand side of an equation. Putting those two together, you could implement the following refactoring:

```haskell
{-# LANGUAGE OverloadedStrings #-}
module Main where
  
import Retrie
  
main :: IO ()
main = runScript $ \opts ->
  [rewrite] <- parseRewrites opts [Adhoc "forall arg. fooOld arg = fooNew arg"]
  return $ apply [setRewriteTransformer stringToFooArg rewrite]
  
argMapping :: [(FastString, String)]
argMapping = [("foo", "Foo"), ("bar", "Bar")]
  
stringToFooArg :: MatchResultTransformer
stringToFooArg _ctxt match
  | MatchResult substitution template <- match
  , Just (HoleExpr expr) <- lookupSubst "arg" substitution
  , L _ (HsLit _ (HsString _ str)) <- astA expr = do
    newExpr <- case lookup str argMapping of
      Nothing ->
        parseExpr $ "error \"invalid argument: " ++ unpackFS str ++ "\""
      Just constructor -> parseExpr constructor
    return $
      MatchResult (extendSubst substitution "arg" (HoleExpr newExpr)) template
  | otherwise = return NoMatch
```

Running this program would create the following diff:

```diff
 module MyModule3 where
  
 baz, bar, quux :: IO ()
-baz = fooOld "foo"
+baz = fooNew Foo
 
-bar = fooOld "bar"
+bar = fooNew Bar

-quux = fooOld "quux"
+quux = fooNew (error "invalid argument: quux")
```

Defining the `stringToFooArg` function requires knowledge of both the Retrie library and GHC's internal AST types. You'll find haddock/hoogle invaluable for both.

# Reporting Bugs/Submitting Patches

To report a bug in the result of a rewrite, please create a test case ([example](tests/inputs/Adhoc.test)) and submit it as an issue or merge request.

To report other bugs, please create a GitHub issue.

[![Build Status](https://travis-ci.com/facebookincubator/retrie.svg?branch=master)](https://travis-ci.com/facebookincubator/retrie)

# License

Retrie is MIT licensed, as found in the [LICENSE](LICENSE) file.

