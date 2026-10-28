import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Unbundled Tensor Power -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTensorPower

noncomputable section

/-! Tensor powers on the homogeneous Picard sheaf without a global
dimension parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
  (A : Over S) [GrpObj A]

include hp hS in
theorem homogeneousPicardClass_tensorPower {T : Over S}
    {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (.op T)}
    (hq : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T q) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T (LineBundleClasses.Construction.tensorPowerClass p q) := by
  intro U f a
  have he := congrArg ((SheafMaps.Construction.relativePicardTensorPower p hp hS A).hom.app (.op U))
    (hq U f a)
  have hn := SheafMaps.Construction.relativePicardTensorPower_toRelativePicard p hp hS A
  have hn' (r : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (.op U)) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hn (.op U)) r
  change ∀ r, (SheafMaps.Construction.relativePicardTensorPower p hp hS A).hom.app (.op U)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U) r) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U) (LineBundleClasses.Construction.tensorPowerClass p r) at hn'
  rw [hn', hn'] at he
  have hchar := Frobenius.Construction.prime_eq_zero_of_map p hS (U ⊗ A).hom
  have hcharT := Frobenius.Construction.prime_eq_zero_of_map p hS (T ⊗ A).hom
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ▷ A).left (LineBundleClasses.Construction.tensorPowerClass p q))) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ▷ A).left (LineBundleClasses.Construction.tensorPowerClass p q))
  erw [LineBundleClasses.Construction.tensorPowerClass_pullback p hp hchar hcharT (f ▷ A).left q,
    LineBundleClasses.Construction.tensorPowerClass_pullback p hp hchar hchar ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left]
  exact he

def homogeneousPicardTensorPowerPresheaf :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A) ⟶ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A) where
  app T := TypeCat.ofHom fun q =>
    ⟨LineBundleClasses.Construction.tensorPowerClass p q.val, homogeneousPicardClass_tensorPower p hp hS A q.property⟩
  naturality {T U} f := by
    ext q
    apply Subtype.ext
    exact (SheafMaps.Construction.relativePicardTensorPowerPresheaf p hp hS A).naturality_apply f q.val

def homogeneousPicardTensorPower : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A) ⟶ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (homogeneousPicardTensorPowerPresheaf p hp hS A)

theorem homogeneousPicardTensorPower_inclusion :
    homogeneousPicardTensorPower p hp hS A ≫ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A) =
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A) ≫ SheafMaps.Construction.relativePicardTensorPower p hp hS A := by
  have he : homogeneousPicardTensorPowerPresheaf p hp hS A ≫ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion A) =
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion A) ≫ SheafMaps.Construction.relativePicardTensorPowerPresheaf p hp hS A := rfl
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp _ _).symm.trans ((congrArg F.map he).trans (F.map_comp _ _))

variable {A}

/-- The endomorphism represented by actual p-th tensor powers of line bundles. -/
def dualPicardTensorPower (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) : D.abelian ⟶ D.abelian :=
  D.representable.homEquiv.symm
    ((homogeneousPicardTensorPower p hp hS A).hom.app (.op D.abelian)
      (D.representable.homEquiv (𝟙 D.abelian)))

theorem dualPicardTensorPower_representation (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)
    {T : Over S} (x : T ⟶ D.abelian) :
    D.representable.homEquiv (x ≫ dualPicardTensorPower p hp hS D) =
      (homogeneousPicardTensorPower p hp hS A).hom.app (.op T)
        (D.representable.homEquiv x) := by
  rw [D.representable.homEquiv_comp, dualPicardTensorPower, Equiv.apply_symm_apply]
  rw [← (homogeneousPicardTensorPower p hp hS A).hom.naturality_apply]
  rw [← D.representable.homEquiv_comp, Category.comp_id]

theorem dualPicardTensorPower_poincare (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)
    {T : Over S} (x : T ⟶ D.abelian) :
    UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (x ≫ dualPicardTensorPower p hp hS D) =
      (SheafMaps.Construction.relativePicardTensorPower p hp hS A).hom.app (.op T) (UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D x) := by
  rw [UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation, dualPicardTensorPower_representation,
    UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun z : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A) ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A => z.hom)
      (homogeneousPicardTensorPower_inclusion p hp hS A)) (.op T))
    (D.representable.homEquiv x)

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTensorPower
