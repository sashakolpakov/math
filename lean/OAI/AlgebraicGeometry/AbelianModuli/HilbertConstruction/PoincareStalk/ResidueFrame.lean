import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.MinimalSource

/-! # Residue Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The closed residue point of the actual dual-zero stalk maps scheme-theoretically to the rational zero section. Its Poincare bundle is therefore trivial; every actual Poincare family also carries the section induced by the abelian zero point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)

theorem Dual.Data.DualAbelianData.poincareZeroStalk_closedResidue_parameter_zero :
    let R := Γ(D.poincareZeroStalkScheme, ⊤);
    let j : Spec (.of (IsLocalRing.ResidueField R)) ⟶ D.poincareZeroStalkScheme :=
      Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R (IsLocalRing.ResidueField R));
    j ≫ D.poincareZeroStalkParameterMap =
      ((j ≫ D.poincareZeroStalkParameterMap) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left := by
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  let B := IsLocalRing.ResidueField R
  let j : Spec (.of B) ⟶ D.poincareZeroStalkScheme := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  have hjSurj : Function.Surjective (algebraMap R B) := by
    exact IsLocalRing.residue_surjective
  have : IsClosedImmersion j := Affine.QuotientCoefficientMap.affineCoordinateMap_isClosedImmersion (algebraMap R B) hjSurj
  let x₀ := η[D.abelian.scheme].left (IsLocalRing.closedPoint K)
  have hj : j (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint (D.abelian.scheme.left.presheaf.stalk x₀) :=
    QuotientResiduePointZero.closedImmersion_singlePoint_localSpec_image (R := D.abelian.scheme.left.presheaf.stalk x₀) j (IsLocalRing.closedPoint B)
  have hpoint : (j ≫ D.poincareZeroStalkParameterMap) (IsLocalRing.closedPoint B) = x₀ :=
    (congrArg (D.abelian.scheme.left.fromSpecStalk x₀) hj).trans Scheme.fromSpecStalk_closedPoint
  have hz : η[D.abelian.scheme].left ≫ D.abelian.scheme.hom = 𝟙 (Spec (.of K)) := η[D.abelian.scheme].w
  exact HilbertConstruction.Field.PointRationalZero.fieldPoint_eq_rational_section_of_point D.abelian.scheme.hom η[D.abelian.scheme].left hz
    (j ≫ D.poincareZeroStalkParameterMap) hpoint

theorem Dual.Data.DualAbelianData.poincareBaseFamily_exists_section
    {T P : Scheme.{u}} (t : T ⟶ D.abelian.scheme.left)
    {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t) :
    ∃ s : T ⟶ P, s ≫ b = 𝟙 T := by
  let c := t ≫ D.abelian.scheme.hom
  let v : T ⟶ A.scheme.left := c ≫ η[A.scheme].left
  have hv : t ≫ D.abelian.scheme.hom = v ≫ A.scheme.hom := by
    change c = (c ≫ η[A.scheme].left) ≫ A.scheme.hom
    exact ((Category.assoc c η[A.scheme].left A.scheme.hom).trans
      ((congrArg (fun w => c ≫ w) η[A.scheme].w).trans (Category.comp_id c))).symm
  let σ : T ⟶ (D.abelian.scheme ⊗ A.scheme).left := pullback.lift t v hv
  have hσ : σ ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom = (𝟙 T) ≫ t :=
    (pullback.lift_fst t v hv).trans (Category.id_comp t).symm
  exact ⟨H.lift σ (𝟙 T) hσ, H.lift_snd σ (𝟙 T) hσ⟩

theorem Dual.Data.DualAbelianData.poincareZeroStalk_residue_family_trivial
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ D.poincareZeroStalkScheme}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) D.poincareZeroStalkParameterMap) :
    let R := Γ(D.poincareZeroStalkScheme, ⊤);
    let j : Spec (.of (IsLocalRing.ResidueField R)) ⟶ D.poincareZeroStalkScheme :=
      Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R (IsLocalRing.ResidueField R));
    Nonempty ((((D.poincare.pullback a).pullback (pullback.fst b j)).sheaf ≅
      Line.Bundles.structureModule (CategoryTheory.Limits.pullback b j))) := by
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  let j : Spec (.of (IsLocalRing.ResidueField R)) ⟶ D.poincareZeroStalkScheme :=
    Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R (IsLocalRing.ResidueField R))
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let HF : IsPullback (a' ≫ a) b' (pullback.fst D.abelian.scheme.hom A.scheme.hom)
      (j ≫ D.poincareZeroStalkParameterMap) := (IsPullback.of_hasPullback b j).paste_horiz H
  obtain ⟨ef⟩ := D.poincareBaseFamily_zero_implies_trivial
    (j ≫ D.poincareZeroStalkParameterMap) HF D.poincareZeroStalk_closedResidue_parameter_zero
  exact ⟨(Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf ≪≫ ef⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
