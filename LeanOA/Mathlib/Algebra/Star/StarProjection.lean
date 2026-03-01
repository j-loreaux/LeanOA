import Mathlib.Algebra.Star.StarProjection

attribute [grind →, aesop safe forward]
  IsStarProjection.isIdempotentElem IsStarProjection.isSelfAdjoint

theorem IsStarProjection.map {A B : Type*} [Mul A] [Star A] [Mul B] [Star B]
    {F : Type*} [FunLike F A B] [StarHomClass F A B] [MulHomClass F A B]
    {x : A} (hx : IsStarProjection x) (f : F) : IsStarProjection (f x) where
  isIdempotentElem := hx.isIdempotentElem.map f
  isSelfAdjoint := hx.isSelfAdjoint.map f
