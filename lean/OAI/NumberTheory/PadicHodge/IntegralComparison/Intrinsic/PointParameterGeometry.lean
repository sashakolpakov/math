import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionCompositeEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothRelativeRank

/-! # Point Parameter Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterGeometry

noncomputable section

/-! The number of point parameters comes from the actual relative
dimension, and their concatenated ideal is the original ideal sheaf
of the composite section in the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U : Y.left.Opens) (hU : IsAffineOpen U) (hsU : ⊤ ≤ s ⁻¹ᵁ (f.left ⁻¹ᵁ U))
  (σ : Type u) [Fintype σ] [Algebra (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  {c m : ℕ} (a : Fin c → Γ(Y.left, U)) (e : Fin m ≃ σ)
  (r : Γ(Y.left, U))
  (D : PointParameterNeighborhood.Data R X Y f s hs U hsU σ a e r)

omit [IsClosedImmersion (Over.Hom.left f)] [Fintype σ] [IsScalarTower R (MvPolynomial σ R) ↑(SmoothClosedSections.ring R X (Over.Hom.left f ⁻¹ᵁ U))] [Algebra.Etale (MvPolynomial σ R) ↑(SmoothClosedSections.ring R X (Over.Hom.left f ⁻¹ᵁ U))] in
theorem generates [IsClosedImmersion (s ≫ f.left)] :
    Ideal.span (Set.range (Fin.append (IdealSheafPrincipalEquations.sequence U r a) D.parameter)) =
      (s ≫ f.left).ker.ideal ⟨Y.left.basicOpen r, hU.basicOpen r⟩ :=
  D.kernel.trans ((SectionCompositeEvaluation.kernel R X Y f s hs
    (Y.left.basicOpen r) D.contains).trans
      (SectionEvaluation.kernel R Y (s ≫ f.left)
        (SectionCompositeEvaluation.over_base R X Y f s hs)
        (Y.left.basicOpen r) D.contains (hU.basicOpen r)))

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  (x : X.left) (hx : f.left x ∈ U)

include hU hx in
theorem exists_principal
    (ha : Ideal.span (Set.range a) = f.left.ker.ideal ⟨U, hU⟩)
    (hareg : RingTheory.Sequence.IsWeaklyRegular Γ(Y.left, U) (List.ofFn a)) :
    ∃ (e : Fin g ≃ σ) (r : Γ(Y.left, U)),
      Nonempty (PointParameterNeighborhood.Data R X Y f s hs U hsU σ a e r) := by
  let p := (hU.preimage f.left).primeIdealOf ⟨x, hx⟩
  have hc := IntegralComparison.Etale.CoordinateRank.card R (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) σ p g
    (SmoothRelativeRank.sections R X g (f.left ⁻¹ᵁ U) (hU.preimage f.left) p)
  let e' : Fin g ≃ σ := (finCongr hc.symm).trans (Fintype.equivFin σ).symm
  obtain ⟨r', h⟩ := PointParameterNeighborhood.exists_principal R X Y f s hs U hU hsU σ a e' ha hareg
  exact ⟨e', r', h⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterGeometry
