import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.UniversalMap

/-! # Universal Property -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.UniversalProperty.CrystallineFrameUniversalProperty

noncomputable section

/-!
# Universal property of the actual crystalline frame extension

A morphism into the frame extension is uniquely specified by its
projection and compatible lifted total coordinates. This is the native
universal property used to relate framed and unframed crystalline sites.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  {P Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}
  (f : P ⟶ Q) (y : σ → P.thickening.ring)
  (hy : ∀ i, P.thickening.reduction (y i) = AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P (a i))

local notation "QR" => Q.thickening.ring
local notation "G" => DividedPowerAlgebra QR (σ →₀ QR)

theorem unique (g : P ⟶ (Functor.CrystallineFrameFunctor.functor p k B σ a).obj Q)
    (hg : g ≫ (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q = f)
    (hcoord : ∀ i, g.ambientMap (Map.CrystallineFrameMap.coordinate a Q i) = y i) :
    g = UniversalMap.CrystallineFrameUniversalMap.map p k B σ a f y hy := by
  let gr : G →+* P.thickening.ring := g.ambientMap.toRingHom
  have hc (t : QR) : gr (algebraMap QR G t) = f.ambientMap t :=
    congrArg (fun h : P ⟶ Q => h.ambientMap t) hg
  have hrel : DividedPowers.IsDPMorphism
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers QR σ (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
      P.thickening.dividedPowers g.ambientMap.toRingHom :=
    g.dp_comp.comp _ (PolynomialThickening.CrystallinePolynomialThickening.identity_isDPMorphism p k Q.residueRing σ Q.thickening)
  have he : gr = (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy).toRingHom := by
    apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate QR σ (RingHom.ker Q.thickening.reduction)
      Q.thickening.dividedPowers P.thickening.ring (RingHom.ker P.thickening.reduction)
      P.thickening.dividedPowers _ _ hrel (Evaluation.CrystallineFrameEvaluation.ambientMap_relativePD p k B σ a f y hy)
    · intro t
      exact (hc t).trans (Evaluation.CrystallineFrameEvaluation.ambientMap_coefficient p k B σ a f y hy t).symm
    · intro i
      have hi := hcoord i
      change gr (algebraMap QR G (Lifts.CrystallineFrameLifts.lift p k B σ a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator QR σ 1 i) = y i at hi
      rw [map_add, hc] at hi
      refine (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hi)).trans ?_
      exact (Evaluation.CrystallineFrameEvaluation.ambientMap_generator p k B σ a f y hy i).symm
  apply Site.Object.Hom.ext
  · exact congrArg (fun h : P ⟶ Q => h.reducedMap) hg
  · exact AlgHom.ext (RingHom.congr_fun he)

include hy in
theorem existsUnique : ∃! g : P ⟶ (Functor.CrystallineFrameFunctor.functor p k B σ a).obj Q,
    g ≫ (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q = f ∧
      ∀ i, g.ambientMap (Map.CrystallineFrameMap.coordinate a Q i) = y i := by
  refine ⟨UniversalMap.CrystallineFrameUniversalMap.map p k B σ a f y hy,
    ⟨UniversalMap.CrystallineFrameUniversalMap.map_projection p k B σ a f y hy,
      UniversalMap.CrystallineFrameUniversalMap.map_coordinate p k B σ a f y hy⟩, ?_⟩
  intro g hg
  exact unique p k B σ a f y hy g hg.1 hg.2

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.UniversalProperty.CrystallineFrameUniversalProperty
