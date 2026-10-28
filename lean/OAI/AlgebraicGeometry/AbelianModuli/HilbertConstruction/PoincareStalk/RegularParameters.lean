import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidueProjectiveDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.GeometricMinimalModel

/-! # Regular Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.RegularParameters

noncomputable section

/-! The actual coefficient ring of the dual-zero-stalk Poincare model has a regular sequence of g maximal-ideal generators, and its residue field has projective dimension g. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry IsLocalRing
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem regular_sequence_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (rs : List R) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs) : Regular.SequenceBasic.RingTheory.Sequence.IsRegular S (rs.map e) := by
  apply (Regular.SequenceBasic.AddEquiv.isRegular_congr (e := e.toAddEquiv) (as := rs) (bs := rs.map e) ?_).mp hreg
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  exact e.map_mul r x

namespace DualAbelianData
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.poincareZeroStalk_regular_parameters :
    ∃ rs : List Γ(D.poincareZeroStalkScheme, ⊤),
      Regular.SequenceBasic.RingTheory.Sequence.IsRegular Γ(D.poincareZeroStalkScheme, ⊤) rs ∧
      Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) ∧ rs.length = g := by
  let x := η[D.abelian.scheme].left (IsLocalRing.closedPoint K)
  let O := D.abelian.scheme.left.presheaf.stalk x
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  let γ : O ≃+* R := (Scheme.ΓSpecIso O).symm.commRingCatIsoToRingEquiv
  obtain ⟨rs, hreg, hgen, hlen⟩ := Rational.PointStalkRegularParameters.rationalPoint_stalk_regular_parameters
    D.abelian.scheme.hom g η[D.abelian.scheme].left η[D.abelian.scheme].w
  refine ⟨rs.map γ, regular_sequence_ringEquiv γ rs hreg, ?_, ?_⟩
  · change Regular.SequenceBasic.Ideal.ofList (rs.map γ.toRingHom) = maximalIdeal R
    rw [← Regular.SequenceBasic.Ideal.map_ofList]
    exact (congrArg (Ideal.map γ.toRingHom) hgen).trans (IsLocalRing.map_ringEquiv_maximalIdeal γ)
  · simpa only [List.length_map] using hlen

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.poincareZeroStalk_residue_projectiveDimension :
    Projective.DimensionBasic.projectiveDimension (ModuleCat.of.{u} Γ(D.poincareZeroStalkScheme, ⊤)
      (ResidueField Γ(D.poincareZeroStalkScheme, ⊤))) = (g : WithBot ℕ∞) := by
  obtain ⟨rs, hreg, hgen, hlen⟩ := D.poincareZeroStalk_regular_parameters
  exact (Rational.PointResidueProjectiveDimension.residue_projectiveDimension_of_regular_parameters Γ(D.poincareZeroStalkScheme, ⊤)
    rs hreg hgen).trans (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) hlen)

end DualAbelianData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.RegularParameters
