module LocalContrib

-- Temporarily I want to avoid external dependencies, until I have
-- time to figure out package management in Idris.

%default total
%access public export

leftOrNothing : Either a b -> Maybe a
leftOrNothing (Left a) = Just a
leftOrNothing _ = Nothing

interface Bifunctor (f : Type -> Type -> Type) where
  bimap : (a -> b) -> (c -> d) -> f a c -> f b d

implementation Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)
