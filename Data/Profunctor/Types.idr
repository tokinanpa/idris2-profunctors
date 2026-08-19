||| This module contains the Profunctor interface itself, along with a few
||| examples of profunctors.
module Data.Profunctor.Types

import Data.Contravariant
import Data.Morphisms

%default total


------------------------------------------------------------------------------
-- Profunctor interface
------------------------------------------------------------------------------


||| An interface for (self-enriched) profunctors `Idr -/-> Idr`.
|||
||| Formally, a profunctor is a binary functor that is contravariant in its
||| first argument and covariant in its second. A common example of a profunctor
||| is the (non-dependent) function type.
|||
||| Implementations can be defined by specifying either `dimap` or both `lmap`
||| and `rmap`.
|||
||| Laws:
||| * `dimap id id = id`
||| * `dimap (f . g) (h . i) = dimap g h . dimap f i`
public export
interface Profunctor p where

  ||| Map over both parameters of a profunctor at the same time, with the
  ||| left function argument mapping contravariantly.
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  ||| Map contravariantly over the first parameter of a profunctor.
  lmap : (a -> b) -> p b c -> p a c
  lmap f = dimap f id

  ||| Map covariantly over the second parameter of a profunctor.
  rmap : (b -> c) -> p a b -> p a c
  rmap = dimap id


export infix 0 :->
||| A transformation between profunctors that preserves their type parameters.
|||
||| Formally, this is a natural transformation of functors `Idrᵒᵖ * Idr => Idr`.
|||
||| If the transformation is `tr`, then we have the following law:
||| * `tr . dimap f g = dimap f g . tr`
public export
0 (:->) : (p, q : k -> k' -> Type) -> Type
p :-> q = forall a, b. p a b -> q a b


------------------------------------------------------------------------------
-- Implementations for existing types
------------------------------------------------------------------------------


public export
Profunctor Morphism where
  dimap f g (Mor h) = Mor (g . h . f)
  lmap f (Mor g) = Mor (g . f)
  rmap = map

namespace Profunctor
  ||| A named implementation of `Profunctor` for function types.
  ||| Use this to avoid having to use a type wrapper like `Morphism`.
  public export
  [Function] Profunctor (\a,b => a -> b) where
    dimap f g h = g . h . f
    lmap = flip (.)
    rmap = (.)

public export
Functor f => Profunctor (Kleislimorphism f) where
  dimap f g (Kleisli h) = Kleisli (map g . h . f)
  lmap f (Kleisli g) = Kleisli (g . f)
  rmap = map


------------------------------------------------------------------------------
-- New profunctor types
------------------------------------------------------------------------------


||| Lift a functor into a profunctor in the return type.
|||
||| This type is equivalent to `Kleislimorphism` except for the polymorphic type
||| of `b`.
public export
record Star {0 k : Type} (f : k -> Type) a (b : k) where
  constructor MkStar
  applyStar : a -> f b

public export
Functor f => Functor (Star f a) where
  map f (MkStar g) = MkStar (map f . g)

public export
Applicative f => Applicative (Star f a) where
  pure = MkStar . const . pure
  MkStar f <*> MkStar g = MkStar (\x => f x <*> g x)

public export
Monad f => Monad (Star f a) where
  MkStar f >>= g = MkStar $ \x => do
    a <- f x
    applyStar (g a) x

public export
Contravariant f => Contravariant (Star f a) where
  contramap f (MkStar g) = MkStar (contramap f . g)


public export
Functor f => Profunctor (Star f) where
  dimap f g (MkStar h) = MkStar (map g . h . f)
  lmap f (MkStar g) = MkStar (g . f)
  rmap f (MkStar g) = MkStar (map f . g)


||| Lift a functor into a profunctor in the argument type.
public export
record Costar {0 k : Type} (f : k -> Type) (a : k) b where
  constructor MkCostar
  applyCostar : f a -> b

public export
Functor (Costar f a) where
  map f (MkCostar g) = MkCostar (f . g)

public export
Applicative (Costar f a) where
  pure = MkCostar . const
  MkCostar f <*> MkCostar g = MkCostar (\x => f x (g x))

public export
Monad (Costar f a) where
  MkCostar f >>= g = MkCostar (\x => applyCostar (g (f x)) x)

public export
Functor f => Profunctor (Costar f) where
  dimap f g (MkCostar h) = MkCostar (g . h . map f)
  lmap f (MkCostar g) = MkCostar (g . map f)
  rmap f (MkCostar g) = MkCostar (f . g)


||| The profunctor that ignores its argument type.
||| Equivalent to `const id` up to isomorphism.
public export
record Tagged {0 k : Type} (a : k) b where
  constructor Tag
  runTagged : b

||| Retag the value with a different type-level parameter.
public export
retag : Tagged a c -> Tagged b c
retag (Tag x) = Tag x

public export
Functor (Tagged a) where
  map f (Tag x) = Tag (f x)

public export
Applicative (Tagged a) where
  pure = Tag
  Tag f <*> Tag x = Tag (f x)

public export
Monad (Tagged a) where
  join = runTagged
  Tag x >>= f = f x

public export
Foldable (Tagged a) where
  foldr f x (Tag y) = f y x
  foldl f x (Tag y) = f x y
  null = const False
  foldlM f x (Tag y) = f x y
  toList (Tag x) = [x]
  foldMap f (Tag x) = f x

public export
Traversable (Tagged a) where
  traverse f (Tag x) = map Tag (f x)

public export
Profunctor Tagged where
  dimap _ f (Tag x) = Tag (f x)
  lmap = const retag
  rmap f (Tag x) = Tag (f x)


||| `Forget r` is equivalent to `Star (Const r)`.
public export
record Forget {0 k : Type} r a (b : k) where
  constructor MkForget
  runForget : a -> r

public export
reforget : Forget r a b -> Forget r a c
reforget (MkForget k) = MkForget k

public export
Functor (Forget r a) where
  map _ = reforget

public export
Contravariant (Forget {k=Type} r a) where
  contramap _ = reforget

public export
Monoid r => Applicative (Forget r a) where
  pure _ = MkForget (const neutral)
  MkForget f <*> MkForget g = MkForget (f <+> g)

public export
Monoid r => Monad (Forget {k=Type} r a) where
  join = reforget
  (>>=) = reforget .: const

public export
Foldable (Forget r a) where
  foldr _ x _ = x
  foldl _ x _ = x
  null = const True
  foldlM _ x _ = pure x
  toList _ = []
  foldMap _ _ = neutral

public export
Traversable (Forget r a) where
  traverse _ = pure . reforget

public export
Profunctor (Forget r) where
  dimap f _ (MkForget k) = MkForget (k . f)
  lmap f (MkForget k) = MkForget (k . f)
  rmap = map


||| `Coforget r` is equivalent to `Costar (Const r)`.
public export
record Coforget {0 k : Type} r (a : k) b where
  constructor MkCoforget
  runCoforget : r -> b

public export
recoforget : Coforget r a c -> Coforget r b c
recoforget (MkCoforget k) = MkCoforget k

public export
Functor (Coforget r a) where
  map f (MkCoforget k) = MkCoforget (f . k)

public export
Bifunctor (Coforget r) where
  bimap _ f (MkCoforget k) = MkCoforget (f . k)
  mapFst _ = recoforget
  mapSnd = map

public export
Applicative (Coforget r a) where
  pure = MkCoforget . const
  MkCoforget f <*> MkCoforget g = MkCoforget (\r => f r (g r))

public export
Monad (Coforget r a) where
  MkCoforget k >>= f = MkCoforget (\r => runCoforget (f $ k r) r)

public export
Profunctor (Coforget r) where
  dimap _ f (MkCoforget k) = MkCoforget (f . k)
  lmap _ = recoforget
  rmap = map


------------------------------------------------------------------------------
-- Identity functor
------------------------------------------------------------------------------

-- A few convenience definitions for use in other modules.

public export
[FunctorId] Functor Prelude.id where
  map = id

public export
[ApplicativeId] Applicative Prelude.id using FunctorId where
  pure = id
  (<*>) = id

public export
[MonadId] Monad Prelude.id using ApplicativeId where
  join = id
  (>>=) = flip id

public export
[FoldableId] Foldable Prelude.id where
  foldr = flip
  foldl = id
  null _ = False
  foldlM = id
  toList = pure
  foldMap = id

public export
[TraversableId] Traversable Prelude.id using FunctorId FoldableId where
  traverse = id
