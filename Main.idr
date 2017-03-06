module Main

import Pruviloj

infixl 9 .>
(.>) : (a -> b) -> (b -> c) -> (a -> c)
(.>) f g = \x => g (f x)

IdempotencyProof : {X : Type} -> (X -> X -> X) -> Type
IdempotencyProof {X} f = (a : X) -> f a a = a

AssociativityProof : {X : Type} -> (X -> X -> X) -> Type
AssociativityProof {X} f = (a : X) ->
                           (b : X) ->
                           (c : X) ->
                           f a (f b c) = f (f a b) c

CommutativityProof : {X : Type} -> (X -> X -> X) -> Type
CommutativityProof {X} f = (a : X) ->
                           (b : X) ->
                           f a b = f b a

LeftUnitalityProof : {X : Type} -> (X -> X -> X) -> X -> Type
LeftUnitalityProof {X} f e = (a : X) -> a = f e a

RightUnitalityProof : {X : Type} -> (X -> X -> X) -> X -> Type
RightUnitalityProof {X} f e = (a : X) -> a = f a e

UnitalityProof : {X : Type} -> (X -> X -> X) -> X -> Type
UnitalityProof {X} f e = (a : X) -> (a = f e a, a = f a e)

record Dual (X : Type) where
  constructor MkDual
  fromDual : X

implementation (Eq x) => Eq (Dual x) where {
  (MkDual x) == (MkDual y) = (x == y)
}

dualInj : (x = y) -> (MkDual x = MkDual y)
dualInj Refl = Refl

interface (Eq X) => MeetSemiLattice (X : Type)
          where {
            meet : X -> X -> X
            meetIsIdempotent  : IdempotencyProof   meet
            meetIsAssociative : AssociativityProof meet
            meetIsCommutative : CommutativityProof meet
          }

interface (Eq X) => JoinSemiLattice (X : Type)
          where {
            join : X -> X -> X
            joinIsIdempotent  : IdempotencyProof   join
            joinIsAssociative : AssociativityProof join
            joinIsCommutative : CommutativityProof join
          }

implementation (JoinSemiLattice t) => MeetSemiLattice (Dual t) where {
  meet a b = MkDual $ join (fromDual a) (fromDual b)
  meetIsIdempotent (MkDual a)
    = dualInj $ joinIsIdempotent a
  meetIsAssociative (MkDual a) (MkDual b) (MkDual c)
    = dualInj $ joinIsAssociative a b c
  meetIsCommutative (MkDual a) (MkDual b)
    = dualInj $ joinIsCommutative a b
}

implementation (MeetSemiLattice t) => JoinSemiLattice (Dual t) where {
  join a b = MkDual $ meet (fromDual a) (fromDual b)
  joinIsIdempotent (MkDual a)
    = dualInj $ meetIsIdempotent a
  joinIsAssociative (MkDual a) (MkDual b) (MkDual c)
    = dualInj $ meetIsAssociative a b c
  joinIsCommutative (MkDual a) (MkDual b)
    = dualInj $ meetIsCommutative a b
}


interface (MeetSemiLattice X)
          => BoundedMeetSemiLattice (X : Type)
          where {
            top : X
            topIsUnital : UnitalityProof meet top
          }

interface (JoinSemiLattice X)
          => BoundedJoinSemiLattice (X : Type)
          where {
            bot : X
            botIsUnital : UnitalityProof join bot
          }

implementation (BoundedMeetSemiLattice t) => BoundedJoinSemiLattice (Dual t)
               where {
                 bot = MkDual top
                 botIsUnital (MkDual a) = let (p1, p2) = topIsUnital a
                                          in (dualInj p1, dualInj p2)
               }

interface (MeetSemiLattice X, JoinSemiLattice X)
          => Lattice (X : Type)
          where {}

interface (BoundedMeetSemiLattice X, BoundedJoinSemiLattice X)
          => BoundedLattice (X : Type)
          where {}

interface (BoundedLattice X)
          => CompleteLattice (X : Type)
          where {
            arbJoin : (I : Type) -> (I -> X) -> X
            arbMeet : (I : Type) -> (I -> X) -> X
            -- LAWS???
          }

ltFromMSL : (M : Type) -> (MeetSemiLattice M) => M -> M -> Bool
ltFromMSL = ?fixme1

interface (MeetSemiLattice X, MeetSemiLattice Y)
          => MonotoneFunction (X : Type) (Y : Type) (f : X -> Y)
          where {
            isMonotone : (a : X) ->
                         (b : X) ->
                         ltFromMSL X a b = ltFromMSL Y (f a) (f b)
          }

implementation (X : Type, CompleteLattice X, MonotoneFunction X X f)
               => CompleteLattice (a : X ** (a = f a))
               where {
               }

main : IO ()
main = pure ()
