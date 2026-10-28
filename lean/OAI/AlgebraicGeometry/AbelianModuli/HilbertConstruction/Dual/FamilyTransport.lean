import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilySheafMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

/-! # Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual

noncomputable section

/-! Transport dual abelian data along an isomorphism of the original abelian family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

/-- The same dual scheme represents the homogeneous Picard sheaf after family isomorphism. -/
def Data.DualAbelianData.familyTransportRepresentable (D : Data.DualAbelianData A) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    B.homogeneousPicardSheaf.obj.RepresentableBy D.abelian.scheme :=
  D.representable.ofIso
    (((sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
      (Homogeneous.FamilyMaps.homogeneousPicardFamilyIso e)).symm)

theorem Data.DualAbelianData.familyTransportRepresentable_origin (D : Data.DualAbelianData A)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (T : Over S) :
    (D.familyTransportRepresentable e).homEquiv (1 : T ⟶ D.abelian.scheme) =
      B.trivialHomogeneousPicardClass T :=
  (congrArg (fun z => (Homogeneous.FamilySheafMaps.homogeneousPicardSheafFamilyMap e.inv).hom.app (.op T) z) (D.origin T)).trans
    (Homogeneous.FamilySheafMaps.homogeneousPicardSheafFamilyMap_trivial e.inv T)

/-- The Poincare bundle pulled back through the family isomorphism. -/
def Data.DualAbelianData.familyTransportPoincare (D : Data.DualAbelianData A) (e : A.scheme ≅ B.scheme) :
    Line.Bundles.LineBundle (D.abelian.scheme ⊗ B.scheme).left :=
  Line.Bundles.LineBundle.pullback (𝟙 D.abelian.scheme ⊗ₘ e.inv).left D.poincare

theorem Data.DualAbelianData.familyTransportPoincare_homogeneous (D : Data.DualAbelianData A)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    B.IsHomogeneousPicardClass D.abelian.scheme (Line.Bundles.LineBundle.classOf (D.familyTransportPoincare e)) :=
  D.poincareHomogeneous.familyMap e.inv

/-- The transported Poincare bundle still gives the universal element. -/
theorem Data.DualAbelianData.familyTransportPoincare_universalClass (D : Data.DualAbelianData A)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (D.familyTransportRepresentable e).homEquiv (𝟙 D.abelian.scheme) =
      (toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf).app (.op D.abelian.scheme)
        ⟨Line.Bundles.LineBundle.classOf (D.familyTransportPoincare e), D.familyTransportPoincare_homogeneous e⟩ :=
  (congrArg (fun z =>
    (Homogeneous.FamilySheafMaps.homogeneousPicardSheafFamilyMap e.inv).hom.app (.op D.abelian.scheme) z) D.universalClass).trans
      (Homogeneous.FamilySheafMaps.homogeneousPicardSheafFamilyMap_toSheafify e.inv D.abelian.scheme
        ⟨Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩)

/-- Normalization at the abelian zero is preserved by the family isomorphism. -/
theorem Data.DualAbelianData.familyTransportPoincare_abelianZero (D : Data.DualAbelianData A)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    Nonempty ((Line.Bundles.LineBundle.pullback
      (lift (𝟙 D.abelian.scheme) (1 : D.abelian.scheme ⟶ B.scheme)).left
        (D.familyTransportPoincare e)).sheaf ≅ Line.Bundles.structureModule D.abelian.scheme.left) := by
  let i := lift (𝟙 D.abelian.scheme) (1 : D.abelian.scheme ⟶ B.scheme)
  let j := lift (𝟙 D.abelian.scheme) (1 : D.abelian.scheme ⟶ A.scheme)
  let p := 𝟙 D.abelian.scheme ⊗ₘ e.inv
  have he : i ≫ p = j := by simp [i, j, p]
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left he)).app D.poincare.sheaf ≪≫
    D.normalizedAtAbelianZero.some⟩

/-- Normalization at the dual zero is preserved by the family isomorphism. -/
theorem Data.DualAbelianData.familyTransportPoincare_dualZero (D : Data.DualAbelianData A)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    Nonempty ((Line.Bundles.LineBundle.pullback
      (lift (1 : B.scheme ⟶ D.abelian.scheme) (𝟙 B.scheme)).left
        (D.familyTransportPoincare e)).sheaf ≅ Line.Bundles.structureModule B.scheme.left) := by
  let i := lift (1 : B.scheme ⟶ D.abelian.scheme) (𝟙 B.scheme)
  let j := lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)
  let p := 𝟙 D.abelian.scheme ⊗ₘ e.inv
  have he : i ≫ p = e.inv ≫ j := by simp [i, j, p]
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left he)).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp e.inv.left j.left).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback e.inv.left).mapIso D.normalizedAtDualZero.some ≪≫
    Line.Bundles.structureModulePullbackIso e.inv.left⟩

/-- Transport all dual data, including the universal normalized Poincare bundle. -/
def Data.DualAbelianData.familyTransport (D : Data.DualAbelianData A) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    Data.DualAbelianData B where
  abelian := D.abelian
  representable := D.familyTransportRepresentable e
  origin := D.familyTransportRepresentable_origin e
  poincare := D.familyTransportPoincare e
  poincareHomogeneous := D.familyTransportPoincare_homogeneous e
  universalClass := D.familyTransportPoincare_universalClass e
  normalizedAtAbelianZero := D.familyTransportPoincare_abelianZero e
  normalizedAtDualZero := D.familyTransportPoincare_dualZero e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual
