import OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

/-! # Homogeneous Tensor Power -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousTensorPower

noncomputable section

/-! Tensor powers on the represented homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

include hp hS in
theorem homogeneousPicardClass_tensorPower {T : Over S}
    {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T)}
    (hq : A.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T (LineBundleClasses.Construction.tensorPowerClass p q) := by
  intro U f a
  have he := congrArg ((SheafMaps.Construction.relativePicardTensorPower p hp hS A.scheme).hom.app (.op U))
    (hq U f a)
  have hn := SheafMaps.Construction.relativePicardTensorPower_toRelativePicard p hp hS A.scheme
  have hn' (r : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op U)) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hn (.op U)) r
  change ∀ r, (SheafMaps.Construction.relativePicardTensorPower p hp hS A.scheme).hom.app (.op U)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) r) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (LineBundleClasses.Construction.tensorPowerClass p r) at hn'
  rw [hn', hn'] at he
  have hchar := Frobenius.Construction.prime_eq_zero_of_map p hS (U ⊗ A.scheme).hom
  have hcharT := Frobenius.Construction.prime_eq_zero_of_map p hS (T ⊗ A.scheme).hom
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ▷ A.scheme).left (LineBundleClasses.Construction.tensorPowerClass p q))) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ▷ A.scheme).left (LineBundleClasses.Construction.tensorPowerClass p q))
  erw [LineBundleClasses.Construction.tensorPowerClass_pullback p hp hchar hcharT (f ▷ A.scheme).left q,
    LineBundleClasses.Construction.tensorPowerClass_pullback p hp hchar hchar (A.translation a).left]
  exact he

def homogeneousPicardTensorPowerPresheaf :
    A.homogeneousPicardPresheaf ⟶ A.homogeneousPicardPresheaf where
  app T := TypeCat.ofHom fun q =>
    ⟨LineBundleClasses.Construction.tensorPowerClass p q.val, homogeneousPicardClass_tensorPower p hp hS A q.property⟩
  naturality {T U} f := by
    ext q
    apply Subtype.ext
    exact (SheafMaps.Construction.relativePicardTensorPowerPresheaf p hp hS A.scheme).naturality_apply f q.val

def homogeneousPicardTensorPower : A.homogeneousPicardSheaf ⟶ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (homogeneousPicardTensorPowerPresheaf p hp hS A)

theorem homogeneousPicardTensorPower_inclusion :
    homogeneousPicardTensorPower p hp hS A ≫ A.homogeneousPicardSheafInclusion =
      A.homogeneousPicardSheafInclusion ≫ SheafMaps.Construction.relativePicardTensorPower p hp hS A.scheme := by
  have he : homogeneousPicardTensorPowerPresheaf p hp hS A ≫ A.homogeneousPicardInclusion =
      A.homogeneousPicardInclusion ≫ SheafMaps.Construction.relativePicardTensorPowerPresheaf p hp hS A.scheme := rfl
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp _ _).symm.trans ((congrArg F.map he).trans (F.map_comp _ _))

variable {A}

/-- The endomorphism represented by actual p-th tensor powers of line bundles. -/
def dualPicardTensorPower (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) : D.abelian.scheme ⟶ D.abelian.scheme :=
  D.representable.homEquiv.symm
    ((homogeneousPicardTensorPower p hp hS A).hom.app (.op D.abelian.scheme)
      (D.representable.homEquiv (𝟙 D.abelian.scheme)))

theorem dualPicardTensorPower_representation (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    {T : Over S} (x : T ⟶ D.abelian.scheme) :
    D.representable.homEquiv (x ≫ dualPicardTensorPower p hp hS D) =
      (homogeneousPicardTensorPower p hp hS A).hom.app (.op T)
        (D.representable.homEquiv x) := by
  rw [D.representable.homEquiv_comp, dualPicardTensorPower, Equiv.apply_symm_apply]
  rw [← (homogeneousPicardTensorPower p hp hS A).hom.naturality_apply]
  rw [← D.representable.homEquiv_comp, Category.comp_id]

theorem dualPicardTensorPower_poincare (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    {T : Over S} (x : T ⟶ D.abelian.scheme) :
    PoincareDetection.Construction.poincareClass D (x ≫ dualPicardTensorPower p hp hS D) =
      (SheafMaps.Construction.relativePicardTensorPower p hp hS A.scheme).hom.app (.op T) (PoincareDetection.Construction.poincareClass D x) := by
  rw [PoincareDetection.Construction.poincareClass_eq_representation, dualPicardTensorPower_representation,
    PoincareDetection.Construction.poincareClass_eq_representation]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun z : A.homogeneousPicardSheaf ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme => z.hom)
      (homogeneousPicardTensorPower_inclusion p hp hS A)) (.op T))
    (D.representable.homEquiv x)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousTensorPower
