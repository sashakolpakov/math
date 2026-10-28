import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionNormalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ImageNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.GlobalImage

/-! # Global Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalImage.IntrinsicCechGlobalImage

noncomputable section

/-! The actual native Čech global-section comparison commutes with the direct-image comparison on inverse-image opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

theorem conjugate_square {C : Type*} [Category* C] {A A' B B' D E : C}
    (u : A ≅ A') (v : B ≅ B') (d : A ⟶ B) (g : B ⟶ D) (h : A ⟶ E) (b : E ⟶ D)
    (hd : d ≫ g = h ≫ b) : (u.inv ≫ d ≫ v.hom) ≫ (v.inv ≫ g) = (u.inv ≫ h) ≫ b := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun k => u.inv ≫ k) hd

variable (R : Type) [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι : Type} (U : ι → Y.left.Opens) (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)

local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).Additive where
  map_add := rfl

theorem square :
    ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).mapHomologicalComplex (.up ℕ)).map
        (Image.IntrinsicCechImage.iso f U F).hom ≫
      (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X (fun i => f.left ⁻¹ᵁ U i)).hom.app F =
    (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R Y U).hom.app ((DeRham.Int.directImage f).obj F) ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Cech.Image.CechImage.preimage f.left) U F.obj).hom := by
  let EY := ((evaluation Y.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)
  let EX := ((evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)
  let G := (Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)
  let V := fun i => f.left ⁻¹ᵁ U i
  let u₀ := PresheafUnit.IntrinsicCechPresheafUnit.iso R Y.left U ((DeRham.Int.directImage f).obj F)
  let v₀ := PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left V F
  let u := EY.mapIso u₀
  let v := EX.mapIso v₀
  let d := EY.map (Cech.Image.CechImage.complexIso R f.left U F.obj).hom
  let s := ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).mapHomologicalComplex (.up ℕ)).map
    (Image.IntrinsicCechImage.iso f U F).hom
  have hm : s = u.inv ≫ d ≫ v.hom :=
    (congrArg EY.map (ImageNaturality.IntrinsicCechImage.map_iso_hom f U F)).trans
      ((EY.map_comp u₀.inv ((Cech.Image.CechImage.complexIso R f.left U F.obj).hom ≫ G.map v₀.hom)).trans
        (congrArg (fun k => EY.map u₀.inv ≫ k)
          (EY.map_comp (Cech.Image.CechImage.complexIso R f.left U F.obj).hom (G.map v₀.hom))))
  have hd := Cech.GlobalImage.CechGlobalImage.square R f F.obj U
  have h := conjugate_square u v d (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X V F.obj).hom
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R Y U ((Cech.Image.CechImage.functor R f.left).obj F.obj)).hom
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Cech.Image.CechImage.preimage f.left) U F.obj).hom hd
  exact (congrArg (fun k => s ≫ k) (GlobalSectionNormalization.IntrinsicCechGlobalSectionNormalization.hom R X V F)).trans
    ((congrArg (fun k => k ≫ (v.inv ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X V F.obj).hom)) hm).trans
      (h.trans (congrArg (fun k => k ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Cech.Image.CechImage.preimage f.left) U F.obj).hom)
        (GlobalSectionNormalization.IntrinsicCechGlobalSectionNormalization.hom R Y U ((DeRham.Int.directImage f).obj F)).symm)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalImage.IntrinsicCechGlobalImage
