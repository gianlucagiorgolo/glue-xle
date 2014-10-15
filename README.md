# Introduction

This is an extremely experimental and buggy wrapper around XLE that
allows you to add semantics to your grammars and get back the readings
for a sentence. It's still very basic and lacks a lot of relevant
features.

I have tested it only on Mac OS X, it should work out of the box on
Linux, but the get it work on Windows some stuff must be changed. If
anyone is interested in trying it on Windows get in contact with me
and we can try to do it.

# Requirements and installation

1. First of all you will need a local copy of XLE, installed and properly
setup. 

2. The wrapper is written in Haskell so the first thing you need to
 compile it is the compiler. The best way to get it is to download the
 [Haskell Platform](https://www.haskell.org/platform/) for your 
 operating system. Install the platform and run `cabal update` to be
 sure to be up to date.

3. You need [Git](http://git-scm.com/) to get the code from
   Bitbucket. You can find Git for your platform here
   [http://git-scm.com/](http://git-scm.com/) (or you can just use the
   package manager for your platform)

4. The first piece of software you need to install is the theorem
   prover. Go to wherever you want to download the theorem prover and
   the type the following:

          git clone https://github.com/gianlucagiorgolo/glue-tp.git glue-tp
          cd glue-tp
          cabal configure
          cabal build
          cabal install

5. Now you can install the wrapper. Again go where you want to download and build the wrapper and then type the following:

		  git clone https://github.com/gianlucagiorgolo/glue-xle.git glue-xle
		  cd glue-xle
		  cabal configure
		  cabal build
		  cabal install

# Usage

You invoke the wrapper with the command `glue-xle` with a single argument which must be the filename of the grammar/lexicon.

A very very simple grammar is included with the source code. So if you are in the `glue-xle` folder you can try the grammar with the following command:

	glue-xle test.lfg

This will start the wrapper that waits for you to type a sentence. The wrapper also starts automatically XLE for you (but see the Known issues section if you are on Mac OS X).

After you type the sentence the wrapper sends it to XLE, which generates the appropriate c-structures and f-structures, which are then used to generate the semantic resources, which are finally passed to the theorem prover. What you get back are the non-equivalent readings. Here is an example of the interaction:

	>>> a cat devours every dog
	Readings for pool 1
	some(cat)(\n.every(dog)(devour(n)))
	every(dog)(\h.some(cat)(\l.devour(l)(h)))
	>>> 

To terminate the wrapper type `:quit` (actually also CTRL-D or CTRL-C should do the work, but use `:quit`).

# Grammar writing

The grammar specification language is an extension of the standard XLE one. We just add semantic informati
on.

## Semantics

Semantic resources are declared in the `LEXICON` section of the grammar. To declare the semantic resources you simply append them to the usual XLE definition of a lexical item, dividing the two with the character `§` (Ash asked me to change it to something else). For example if the standard lexical entry for the word *dog* is:

	dog N * (^ PRED)='dog'.

the same entry becomes:

	dog N * (^ PRED)='dog' § dog :: (^_s VAR):e --o (^_s RESTR):t.

The semantic part of the lexical entries has two parts: 1. a *lambda term* representing the meaning of the resource, 2. a recipe to construct a linear formula (glue formula) from the sigma-projection of the current f-structure.

### Syntax for lambda terms
Literals are indicated by single quotes.

~~~~
LambdaTerm := Constant | Variable | Application | LambdaAbstraction | Pair | FirstProjection | SecondProjection 
Constant := [a-z][a-zA-Z1-0]* # any sequence of letter and digits starting with a lower case letter
Variable := [A-Z][a-zA-Z1-0]* # any sequence of letter and digits starting with an upper case letter
Application := '(' LambdaTerm ' ' LambdaTerm ')' # The outer parentheses are optional. Application is left-associative so `(a b c)` stands for `((a b) c)`.
LambdaAbstraction := '\' Variable '->' LambdaTerm # Lambda abstraction is right-associative
Pair := '<' LambdaTerm ',' LambdaTerm '>'
FirstProjection := '1(' LambdaTerm ')'
SecondProjection := '2(' LambdaTerm ')'
~~~~

Also unit and bind are implemented but don't use them for now.

### Syntax for linear formula recipes

The syntax is composed of two parts: one for the f-structures and sigma-structures path, and one for the linear logic component.

The syntax for f-structures path is the same you are used to from XLE, in particular `^` is used for the up arrow metavariable. Sigma projections are signaled with `_s`. Outside-in and inside-out paths for sigma structures are defined in the same way. 

Atomic linear formulae must be typed. You do so by appending the type to the formula the type (which is any sequence of letters and digits starting with a lower case letter) and separating the two with a colon `:`. An atomic formula is either a sigma-structure or a variable (any sequence of letter and digits starting with an upper case letter).

There are two linear connectives (actually three, but again don't use diamond for now):

1. `--o`, linear implication

2. `*`, linear tensor

Both are right-associative. You can use square brackets around the conjuncts:

	X:a --o [[Y:b * Z:c] --o W:d]

## Semantic templates

You can specify specific semantic templates in a dedicated `SEMANTICTEMPLATES` section. Semantic templates are declared in the same way you declare standard templates, but are expanded by the wrapper and not by XLE.

# Known Issues and limitations

1. On Mac OS X if X11 (XQuartz nowadays) is not running the wrapper
   will hang after starting XLE. Just kill it with CTRL-C and restart
   it, it should work.

2. For some arcane reason I still have to understand, if the XLE can't
   find any parse it will give you back the last successful parse
   (possibly one coming from a previous session). So if the wrapper
   gives you back a reading that has nothing to do with the sentence
   you typed, the problem may be with the parsing process. 

3. At this point only single file grammars are supported.

4. No semantics for rules for now.

5. No ambiguity or multiple resources (multiple resources can be simulated with pairs).

6. No Kleene operations.

7. Don't use monads for now.
