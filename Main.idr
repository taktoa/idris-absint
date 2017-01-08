module Main

IdempotencyProof : (X : Type) -> (X -> X -> X) -> Type
IdempotencyProof X f = (a : X) -> f a a = a

AssociativityProof : (X : Type) -> (X -> X -> X) -> Type
AssociativityProof X f = (a : X) ->
                         (b : X) ->
                         (c : X) ->
                         f a (f b c) = f (f a b) c

CommutativityProof : (X : Type) -> (X -> X -> X) -> Type
CommutativityProof X f = (a : X) ->
                         (b : X) ->
                         f a b = f b a

LeftUnitalityProof : (X : Type) -> (X -> X -> X) -> X -> Type
LeftUnitalityProof X f e = (a : X) -> a = f e a

RightUnitalityProof : (X : Type) -> (X -> X -> X) -> X -> Type
RightUnitalityProof X f e = (a : X) -> a = f a e

UnitalityProof : (X : Type) -> (X -> X -> X) -> X -> Type
UnitalityProof X f e = (LeftUnitalityProof X f e, RightUnitalityProof X f e)

record Dual (X : Type) where
  constructor MkDual
  fromDual : X
  
implementation (Eq x) => Eq (Dual x) where {

}

interface (Eq X) => MeetSemiLattice (X : Type)
          where {
            meet : X -> X -> X
            meetIsIdempotent  : IdempotencyProof   X meet
            meetIsAssociative : AssociativityProof X meet
            meetIsCommutative : CommutativityProof X meet
          }

interface (Eq X) => JoinSemiLattice (X : Type)
          where {
            join : X -> X -> X
            joinIsIdempotent  : IdempotencyProof   X join
            joinIsAssociative : AssociativityProof X join
            joinIsCommutative : CommutativityProof X join
          }
  
implementation (MeetSemiLattice x)
               => JoinSemiLattice (Dual x)
               where {
                 join a b = MkDual $ meet (fromDual a) (fromDual b)
                 joinIsIdempotent (MkDual a) = ?fixmeDual
                 joinIsAssociative = ?fixme
                 joinIsCommutative = ?fixme
               }


interface (MeetSemiLattice X)
          => BoundedMeetSemiLattice (X : Type)
          where {
            top : X
            topIsUnital : UnitalityProof X meet top
          }

interface (JoinSemiLattice X)
          => BoundedJoinSemiLattice (X : Type)
          where {
            bot : X
            botIsUnital : UnitalityProof X join bot
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
