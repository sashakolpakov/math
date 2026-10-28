import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

/-! # Dual Representing Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualRepresentingTransport

noncomputable section

/-! Transport the representing abelian scheme of actual dual data,
including the Poincare line and both zero normalizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
universe u
variable {S : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (e : B.scheme ≅ D.abelian.scheme)

def dualRepresentingPoincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ A.scheme).left :=
  D.poincare.pullback (e.hom ▷ A.scheme).left

theorem dualRepresentingPoincare_homogeneous :
    A.IsHomogeneousPicardClass B.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (dualRepresentingPoincare D e)) :=
  D.poincareHomogeneous.pullback A e.hom

theorem dualRepresenting_origin [IsMonHom e.hom] (T : Over S) :
    (D.representable.ofIsoObj e).homEquiv (1 : T ⟶ B.scheme) =
      A.trivialHomogeneousPicardClass T := by
  change D.representable.homEquiv ((1 : T ⟶ B.scheme) ≫ e.hom) = _
  rw [MonObj.one_comp]
  exact D.origin T

theorem dualRepresenting_universalClass :
    (D.representable.ofIsoObj e).homEquiv (𝟙 B.scheme) =
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op B.scheme)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (dualRepresentingPoincare D e), dualRepresentingPoincare_homogeneous D e⟩ := by
  change D.representable.homEquiv (𝟙 B.scheme ≫ e.hom) = _
  rw [Category.id_comp, ← Category.comp_id e.hom, D.representable.homEquiv_comp, D.universalClass]
  exact ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).naturality_apply
    e.hom.op ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩).symm

theorem dualRepresenting_abelianZero :
    Nonempty (((dualRepresentingPoincare D e).pullback
      (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left) := by
  let i := lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)
  let j := lift (𝟙 D.abelian.scheme) (1 : D.abelian.scheme ⟶ A.scheme)
  let p := e.hom ▷ A.scheme
  have he : i ≫ p = e.hom ≫ j := by simp [i, j, p]
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left he)).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp e.hom.left j.left).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback e.hom.left).mapIso D.normalizedAtAbelianZero.some ≪≫
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso e.hom.left⟩

theorem dualRepresenting_dualZero [IsMonHom e.hom] :
    Nonempty (((dualRepresentingPoincare D e).pullback
      (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) := by
  let i := lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)
  let j := lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)
  let p := e.hom ▷ A.scheme
  have he : i ≫ p = j := by simp [i, j, p]
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left he)).app D.poincare.sheaf ≪≫
    D.normalizedAtDualZero.some⟩

def dualRepresentingTransport [IsMonHom e.hom] : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A where
  abelian := B
  representable := D.representable.ofIsoObj e
  origin := dualRepresenting_origin D e
  poincare := dualRepresentingPoincare D e
  poincareHomogeneous := dualRepresentingPoincare_homogeneous D e
  universalClass := dualRepresenting_universalClass D e
  normalizedAtAbelianZero := dualRepresenting_abelianZero D e
  normalizedAtDualZero := dualRepresenting_dualZero D e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualRepresentingTransport
