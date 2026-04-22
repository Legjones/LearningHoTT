import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import Mathlib.Topology.UnitInterval
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.ULift


universe u

open Set Convex Bornology Simplicial CategoryTheory.Functor CategoryTheory SSet Subcomplex

--The retract, as simplicial sets, of the standard simplex to its horns
def horn_retract_frm_std (n : ℕ) (i : Fin (n + 1)) : NatTrans Δ[n] Λ[n,i] :=
{
  app := by
    sorry
  naturality := by
    sorry
}

def horn_incl_std (n : ℕ) (i : Fin (n + 1)) : NatTrans Λ[n,i] Δ[n] :=
{
  app := by
    sorry
  naturality := by
    sorry
}

--The inclusion of the subcomplex stuff is dealt with in "Subcomplex"... ι horn...
--Below is expressing the composition is an identity...
lemma horn_retract_frm_std_isretract (n : ℕ) (i : Fin (n + 1)) :
((ι Λ[n,i]) ≫ (horn_retract_frm_std n i)) = (NatTrans.id (toSSetFunctor.obj Λ[n,i])) := by
  sorry

--Using something like the following, with geometric realization, it should be a quick
--corollary that we have our retraction on geometric realization too...
def geo_horn_retract_frm_std (n : ℕ) (i : Fin (n + 1)) : |Δ[n]| → |Λ[n,i]| :=
{
 sorry
}
/--
We then need some kind of lemma identifying the lifting diagrams we want to complete
for simplicial sets, see the Kan condition, with the geometric version. I.e. we want a
(natural) bijection between diagrams

Λ[n,i] -> S_*(X)                  |Λ[n,i]| -> X
   |                  <--->          |
   v                                 v
  Δ[n]                             |Δ[n]|

  We should be able to accomplish this by applying the fact that geometric realization
  is left adjoint to the singular chains functor, for the top "row" of maps. We can kind
  of not worry about the verticals in this diagram, because of how we phrased things above.
  In particular:
-/

/--
We can then show we have our lifting criteria by starting with the diagram on the left, above,
going to one on the right, using geo_horn_retract_frm_std to construct a lifting there,
then passing back through our adjunction identification the lift.

The only thing I think we have to be (particularly) careful about is in checking that our
lift pushed through this adjunction still makes the diagram commute. In particular we need
some compatibility with what we mean by the verticals on each side, but this should just
follow from naturality of the adjunction identification in the first coordinate.
-/
