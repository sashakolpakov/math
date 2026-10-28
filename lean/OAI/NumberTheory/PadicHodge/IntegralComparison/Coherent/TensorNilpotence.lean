import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.HilbertFiltration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine

/-! # Tensor Nilpotence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorNilpotence.ProjectiveK

noncomputable section

/-! Tensor differences for arbitrary actual invertible sheaves lower the
Hilbert filtration in any characteristic. Mixed products therefore vanish
once their total order exceeds the Hilbert degree of the class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration.Dimension

universe u
attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory

def lineBundleOfInvertible {A : Scheme.{u}} (L : A.Modules)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A where
  sheaf := L
  locallyTrivial x := by
    obtain ⟨ι, U, hU, he⟩ := hL
    have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨U i, hi, he i⟩

variable {K : Type u} [Field K] [Infinite K] {r : ℕ} {A : Scheme.{u}} [IsIntegral A]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

theorem coherentTensorDifference_mem_hilbertFiltration
    (L : A.Modules) (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) (d : ℕ)
    (x : KTheory.Projective.CoherentK0 A) (hx : x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j (d + 1)) :
    KTheory.Projective.coherentTensorDifference L hL x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j d := by
  let : L.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent hL
  let : L.IsFiniteType :=
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.isFiniteType_of_isLineBundle L (lineBundleOfInvertible L hL).locallyTrivial
  obtain ⟨b, hb⟩ := AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration.Dimension.closedProjective_eventually_hasFiniteGlobalGenerators f L j
  let H := (Scheme.Modules.pullback f).obj
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j b)
  have hH : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible H :=
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible j b).pullback f
  let HB := lineBundleOfInvertible H hH
  let D := AlgebraicGeometry.Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual HB
  have hD : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible D.sheaf := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible D
  have hLH : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible (L ⊗ H) :=
    (hL.tensorObj hH).of_iso (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso L H)
  let T := KTheory.Projective.coherentTensorEnd L hL
  let U := KTheory.Projective.coherentTensorEnd H hH
  let V := KTheory.Projective.coherentTensorEnd D.sheaf hD
  have hUV : U * V = 1 := by
    change (KTheory.Projective.coherentTensorK0 H hH).comp (KTheory.Projective.coherentTensorK0 D.sheaf hD) =
      AddMonoidHom.id (KTheory.Projective.CoherentK0 A)
    rw [KTheory.Projective.coherentTensorK0_comp]
    have e : D.sheaf ⊗ H ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A :=
      AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.evaluation_swap HB ≪≫ AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso A
    exact (KTheory.Projective.coherentTensorK0_congr _ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit e).trans
      (KTheory.Projective.coherentTensorK0_unit A)
  have hTU : T * U = KTheory.Projective.coherentTensorEnd (L ⊗ H) hLH := by
    change (KTheory.Projective.coherentTensorK0 L hL).comp (KTheory.Projective.coherentTensorK0 H hH) =
      KTheory.Projective.coherentTensorK0 (L ⊗ H) hLH
    rw [KTheory.Projective.coherentTensorK0_comp]
    exact KTheory.Projective.coherentTensorK0_congr _ hLH (β_ H L)
  apply AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference.endomorphism_difference_mem_of_product
    (HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j (d + 1)) (HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j d)
    T U V hUV ?_ ?_ ?_ x hx
  · intro y hy
    exact HilbertFiltration.ProjectiveK.coherentTensorK0_mem_hilbertFiltration f j D (d + 1) y hy
  · intro y hy
    rw [hTU]
    exact HilbertFiltration.ProjectiveK.generated_tensorDifference_mem_hilbertFiltration f j
      (lineBundleOfInvertible (L ⊗ H) hLH) (hb b le_rfl) d y hy
  · intro y hy
    exact HilbertFiltration.ProjectiveK.generated_tensorDifference_mem_hilbertFiltration f j HB
      ((AlgebraicGeometry.SheafCohomology.Projective.GlobalGeneration.Dimension.positiveTwist_hasFiniteGlobalGenerators (R := K) j b).pullback f) d y hy

theorem coherentTensorDifference_pow_mem_hilbertFiltration
    (L : A.Modules) (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) (n d : ℕ)
    (x : KTheory.Projective.CoherentK0 A) (hx : x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j (d + n)) :
    (KTheory.Projective.coherentTensorDifference L hL ^ n) x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j d :=
  AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference.endomorphism_pow_mem_filtration (HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j)
    (KTheory.Projective.coherentTensorDifference L hL)
    (coherentTensorDifference_mem_hilbertFiltration f j L hL) n d x hx

theorem coherentTensorDifference_pow_eq_zero_of_hilbertFiltration
    (L : A.Modules) (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L) (d : ℕ)
    (x : KTheory.Projective.CoherentK0 A) (hx : x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j d) :
    (KTheory.Projective.coherentTensorDifference L hL ^ d) x = 0 :=
  AlgebraicGeometry.SheafCohomology.Projective.FilteredEndomorphismDifference.endomorphism_pow_eq_zero_of_filtration (HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j)
    (HilbertFiltration.ProjectiveK.coherentHilbertFiltration_zero f j) (KTheory.Projective.coherentTensorDifference L hL)
    (coherentTensorDifference_mem_hilbertFiltration f j L hL) d x hx

theorem coherentTensorDifference_mixed_eq_zero
    (L M N : A.Modules) (hL : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible M) (hN : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible N)
    (a b c d : ℕ) (hd : d ≤ a + b + c) (x : KTheory.Projective.CoherentK0 A)
    (hx : x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j d) :
    (KTheory.Projective.coherentTensorDifference L hL ^ a)
      ((KTheory.Projective.coherentTensorDifference M hM ^ b)
        ((KTheory.Projective.coherentTensorDifference N hN ^ c) x)) = 0 := by
  have hx' : x ∈ HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j (a + b + c) :=
    HilbertFiltration.ProjectiveK.coherentHilbertFiltration_mono f j hd hx
  have hn := coherentTensorDifference_pow_mem_hilbertFiltration f j N hN c (a + b) x hx'
  have hm := coherentTensorDifference_pow_mem_hilbertFiltration f j M hM b a
    ((KTheory.Projective.coherentTensorDifference N hN ^ c) x) hn
  exact coherentTensorDifference_pow_eq_zero_of_hilbertFiltration f j L hL a _ hm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorNilpotence.ProjectiveK
