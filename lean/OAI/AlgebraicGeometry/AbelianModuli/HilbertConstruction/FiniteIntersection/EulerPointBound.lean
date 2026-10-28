import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulCokernelNonzeroStalks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SupportStalkEulerBound

/-! # Euler Point Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.EulerPointBound

noncomputable section

/-! A finite configuration in the common zeros of g sections on a
proper smooth g-dimensional scheme is bounded by the actual mixed
Euler difference. The proof counts nonzero cokernel stalks, so no
reducedness or transverse-intersection hypothesis is imposed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance pointBoundLineBundle_quasicoherent {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    L.sheaf.IsQuasicoherent := L.isQuasicoherent
local instance pointBoundLineBundle_finiteType {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    L.sheaf.IsFiniteType := L.isFiniteType

theorem finiteIntersection_card_le_mixedEulerDifference
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] (g : ℕ) (hg : 0 < g) [SmoothOfRelativeDimension g p]
    (M : Line.Bundles.LineBundle X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (hlen : bs.length = g)
    (hf : (MixedKoszulGeometricSupport.mixedSectionZeroSet bs).Finite) (S : Finset X)
    (hS : ∀ x ∈ S, x ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet bs) :
    (S.card : ℤ) ≤ MixedKoszulEulerDifference.mixedLineBundleEulerDifference X bs (LineBundle.EulerShifts.lineBundleClassEuler p) (Line.Bundles.LineBundle.classOf M) := by
  have := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M.sheaf bs).1
  have := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M.sheaf bs).2
  have h := HilbertConstruction.Finite.SupportStalkEulerBound.finiteSupport_nonzeroStalk_count_le_euler p (MixedKoszulCokernelEuler.mixedKoszulCokernel M.sheaf bs)
    (MixedKoszulCokernelSupport.mixedKoszulCokernel_support_finite M.sheaf bs hf) S
    (fun x hx => KoszulCokernelNonzeroStalks.mixedKoszulCokernel_stalk_nonzero M bs x (hS x hx))
  rwa [MixedKoszulCokernelEuler.smoothMixedKoszulCokernel_euler p g hg M bs hlen hf] at h

theorem finiteIntersection_configuration_card_le_mixedEulerDifference
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] (g : ℕ) (hg : 0 < g) [SmoothOfRelativeDimension g p]
    (M : Line.Bundles.LineBundle X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (hlen : bs.length = g)
    (hf : (MixedKoszulGeometricSupport.mixedSectionZeroSet bs).Finite) {ι : Type v} [Finite ι]
    (x : ι → X) (hx : Function.Injective x) (hzero : ∀ i, x i ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet bs) :
    (Nat.card ι : ℤ) ≤ MixedKoszulEulerDifference.mixedLineBundleEulerDifference X bs (LineBundle.EulerShifts.lineBundleClassEuler p) (Line.Bundles.LineBundle.classOf M) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let S : Finset X := Finset.univ.image x
  have hcard : S.card = Nat.card ι := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Nat.card_eq_fintype_card]
  have h := finiteIntersection_card_le_mixedEulerDifference p g hg M bs hlen hf S (by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hzero i)
  simpa only [hcard] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.EulerPointBound
