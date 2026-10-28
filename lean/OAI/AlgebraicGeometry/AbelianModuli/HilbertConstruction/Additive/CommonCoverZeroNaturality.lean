import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverDegreeZero

/-! # Common Cover Zero Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverZeroNaturality

noncomputable section

/-! The degree-zero common-cover comparison commutes with every actual
additive-sheaf morphism. It requires only the covering property. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

theorem additiveCommonCoverZeroCohomologyIso_naturality
    {X P : Scheme.{u}} (a : P ⟶ X) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    {F G : P.carrier.Sheaf AddCommGrpCat.{u}} (e : F ⟶ G) :
    HomologicalComplex.homologyMap
      ((cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map a.base).op e.hom)) 0 ≫
        (CommonCoverDegreeZero.additiveCommonCoverZeroCohomologyIso a U hU G).hom =
      (CommonCoverDegreeZero.additiveCommonCoverZeroCohomologyIso a U hU F).hom ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map e := by
  let V := fun i => a ⁻¹ᵁ U i
  let hV := Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU
  let k := HomologicalComplex.homologyMap
    ((cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map a.base).op e.hom)) 0
  let l := HomologicalComplex.homologyMap ((cechComplexFunctor V).map e.hom) 0
  let pF := HomologicalComplex.homologyMap (CechPushforward.additiveCechPushforwardComplexIso a F.obj U).inv 0
  let pG := HomologicalComplex.homologyMap (CechPushforward.additiveCechPushforwardComplexIso a G.obj U).inv 0
  let tF := IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso V F hV
  let tG := IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso V G hV
  let r := e.hom.app (op ⊤)
  let q := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map e
  let F' : CategoryTheory.Sheaf (Opens.grothendieckTopology P.carrier) AddCommGrpCat.{u} := F
  let G' : CategoryTheory.Sheaf (Opens.grothendieckTopology P.carrier) AddCommGrpCat.{u} := G
  let HF : AddCommGrpCat.{u} := (CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology P.carrier) 0).obj F'
  let HG : AddCommGrpCat.{u} := (CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology P.carrier) 0).obj G'
  let eF : HF ≃+ F'.obj.obj (op ⊤) := CategoryTheory.Sheaf.H.equiv₀ F' isTerminalTop
  let eG : HG ≃+ G'.obj.obj (op ⊤) := CategoryTheory.Sheaf.H.equiv₀ G' isTerminalTop
  let zF : F'.obj.obj (op ⊤) ≅ HF := eF.symm.toAddCommGrpIso
  let zG : G'.obj.obj (op ⊤) ≅ HG := eG.symm.toAddCommGrpIso
  have hp : k ≫ pG = pF ≫ l := by
    change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      CechPushforwardNaturality.additiveCechPushforwardComplexIso_inv_naturality]
  have ht : r ≫ tG.hom = tF.hom ≫ l :=
    (IntrinsicCech.TopDegreeZero.cechTopSectionsToHZero_naturality V e).symm
  have ht' : l ≫ tG.inv = tF.inv ≫ r := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun v => tF.inv ≫ v ≫ tG.inv) ht.symm
  have hz : r ≫ zG.hom = zF.hom ≫ q := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (CategoryTheory.Sheaf.H.equiv₀_symm_naturality isTerminalTop e x).symm
  change k ≫ (pG ≫ (tG.inv ≫ zG.hom)) = (pF ≫ (tF.inv ≫ zF.hom)) ≫ q
  calc
    _ = pF ≫ (l ≫ (tG.inv ≫ zG.hom)) := by rw [← Category.assoc, hp, Category.assoc]
    _ = pF ≫ (tF.inv ≫ (r ≫ zG.hom)) := by rw [← Category.assoc l, ht', Category.assoc]
    _ = pF ≫ (tF.inv ≫ (zF.hom ≫ q)) := by rw [hz]
    _ = _ := by simp only [Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverZeroNaturality
