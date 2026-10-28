import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveExtPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ConstantPullback
import OAI.AlgebraicGeometry.Comparison.Betti.ExtCoefficientFunctor

/-! # Ext Derived Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtDerivedPullback

noncomputable section

/-! Compatibility of Ext pullback with actual derived constant-sheaf pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace

def locallyConstantExtDerivedEquiv (M : TopCat.{0}) (n : ℕ) :
    Ext.{1} (ConstantSheafSections.standardConstantSheaf M) (InjectiveExtPullback.locallyConstantCoefficients M) n ≃ₗ[ℂ]
      Derived.DerivedSheafBetti.constantDerivedCohomology M n := by
  let e : InjectiveExtPullback.locallyConstantCoefficients M ≅ ConstantSheafSections.standardConstantSheaf M :=
    (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).symm
  let et := (shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves M)) (n : ℤ)).mapIso
    ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).mapIso e)
  exact (Ext.homLinearEquiv (C := ConstantSheafSections.ComplexSheaves M) (R := ℂ)).trans (Linear.homCongr ℂ (Iso.refl _) et)

theorem locallyConstantExtDerivedEquiv_apply (M : TopCat.{0}) (n : ℕ)
    (a : Ext.{1} (ConstantSheafSections.standardConstantSheaf M) (InjectiveExtPullback.locallyConstantCoefficients M) n) :
    locallyConstantExtDerivedEquiv M n a = a.hom ≫
      ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map
        (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).inv)⟦(n : ℤ)⟧' := by
  change (𝟙 _ ≫ a.hom) ≫ _ = _
  rw [Category.id_comp]
  rfl

variable {M N : TopCat.{0}} (f : M ⟶ N)

theorem locallyConstantPullbackIso_to_constant :
    (TopologicalSheafPullback.locallyConstantPullbackIso f).hom ≫ (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).inv =
      (TopologicalSheafPullback.sheafInverseImage f).map (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N).inv ≫ (TopologicalSheafPullback.constantPullbackIso f).hom := by
  let eN : ConstantSheafSections.standardConstantSheaf N ≅ InjectiveExtPullback.locallyConstantCoefficients N := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N
  let eM : ConstantSheafSections.standardConstantSheaf M ≅ InjectiveExtPullback.locallyConstantCoefficients M := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M
  change ((TopologicalSheafPullback.sheafInverseImage f).map eN.inv ≫ (TopologicalSheafPullback.constantPullbackIso f).hom ≫ eM.hom) ≫ eM.inv = _
  erw [Category.assoc ((TopologicalSheafPullback.sheafInverseImage f).map eN.inv) ((TopologicalSheafPullback.constantPullbackIso f).hom ≫ eM.hom) eM.inv,
    Category.assoc (TopologicalSheafPullback.constantPullbackIso f).hom eM.hom eM.inv, eM.hom_inv_id, Category.comp_id]
  rfl

theorem derivedLocallyConstantPullback_to_constant :
    ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategorySingleFunctor 0).hom.app (InjectiveExtPullback.locallyConstantCoefficients N) ≫
      (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map (TopologicalSheafPullback.locallyConstantPullbackIso f).hom ≫
        (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map
          (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).inv =
      (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory.map
          ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves N) 0).map
            (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N).inv) ≫ (Derived.ConstantPullback.derivedConstantPullbackIso f).hom := by
  let S := DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0
  let eN : ConstantSheafSections.standardConstantSheaf N ≅ InjectiveExtPullback.locallyConstantCoefficients N := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N
  have h := ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategorySingleFunctor 0).hom.naturality eN.inv
  erw [← S.map_comp (TopologicalSheafPullback.locallyConstantPullbackIso f).hom (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).inv,
    locallyConstantPullbackIso_to_constant,
    S.map_comp ((TopologicalSheafPullback.sheafInverseImage f).map eN.inv) (TopologicalSheafPullback.constantPullbackIso f).hom,
    ← Category.assoc, ← h]
  exact Category.assoc _ _ _

theorem locallyConstantExtPullback_hom (n : ℕ)
    (a : Ext.{1} (ConstantSheafSections.standardConstantSheaf N) (InjectiveExtPullback.locallyConstantCoefficients N) n) :
    (InjectiveExtPullback.locallyConstantExtPullback f n a).hom =
      (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map (TopologicalSheafPullback.constantPullbackIso f).inv ≫
        (((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategorySingleFunctor 0).inv.app (ConstantSheafSections.standardConstantSheaf N) ≫
          ShiftedHom.map a.hom (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory ≫
            (((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategorySingleFunctor 0).hom.app
              (InjectiveExtPullback.locallyConstantCoefficients N))⟦(n : ℤ)⟧') ≫
          ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map
            (TopologicalSheafPullback.locallyConstantPullbackIso f).hom)⟦(n : ℤ)⟧' := by
  let s : ConstantSheafSections.standardConstantSheaf M ⟶ (TopologicalSheafPullback.sheafInverseImage f).obj (ConstantSheafSections.standardConstantSheaf N) :=
    (TopologicalSheafPullback.constantPullbackIso f).inv
  let t : (TopologicalSheafPullback.sheafInverseImage f).obj (InjectiveExtPullback.locallyConstantCoefficients N) ⟶ InjectiveExtPullback.locallyConstantCoefficients M :=
    (TopologicalSheafPullback.locallyConstantPullbackIso f).hom
  exact ExtCoefficientFunctor.exactFunctorCoefficientHom.{1, 1} (C := ConstantSheafSections.ComplexSheaves N) (D := ConstantSheafSections.ComplexSheaves M)
    (TopologicalSheafPullback.sheafInverseImage f) s t n a

theorem locallyConstantExtDerivedEquiv_naturality (n : ℕ)
    (a : Ext.{1} (ConstantSheafSections.standardConstantSheaf N) (InjectiveExtPullback.locallyConstantCoefficients N) n) :
    locallyConstantExtDerivedEquiv M n (InjectiveExtPullback.locallyConstantExtPullback f n a) =
      Derived.ConstantPullback.constantDerivedPullback f n (locallyConstantExtDerivedEquiv N n a) := by
  let F := (TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategory
  let S := shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves M)) (n : ℤ)
  let eN : ConstantSheafSections.standardConstantSheaf N ≅ InjectiveExtPullback.locallyConstantCoefficients N := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N
  let eM : ConstantSheafSections.standardConstantSheaf M ≅ InjectiveExtPullback.locallyConstantCoefficients M := Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M
  let q := (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves N) 0).map eN.inv
  let d := ShiftedHom.map a.hom F
  let s := (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map (TopologicalSheafPullback.constantPullbackIso f).inv
  let t := ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategorySingleFunctor 0).inv.app (ConstantSheafSections.standardConstantSheaf N)
  let z := ((TopologicalSheafPullback.sheafInverseImage f).mapDerivedCategorySingleFunctor 0).hom.app (InjectiveExtPullback.locallyConstantCoefficients N)
  let l : (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).obj
      ((TopologicalSheafPullback.sheafInverseImage f).obj (InjectiveExtPullback.locallyConstantCoefficients N)) ⟶
        (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).obj (InjectiveExtPullback.locallyConstantCoefficients M) :=
    (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map (TopologicalSheafPullback.locallyConstantPullbackIso f).hom
  let r := (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).map eM.inv
  let e := Derived.ConstantPullback.derivedConstantPullbackIso f
  have hm : ShiftedHom.map (a.hom ≫ q⟦(n : ℤ)⟧') F =
      ShiftedHom.map a.hom F ≫ S.map (F.map q) := by
    have h := ShiftedHom.map_comp a.hom (ShiftedHom.mk₀ (0 : ℤ) rfl q) (zero_add (n : ℤ)) F
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using h
  have ht : S.map z ≫ S.map l ≫ S.map r = S.map (F.map q) ≫ S.map e.hom := by
    have h : z ≫ l ≫ r = F.map q ≫ e.hom := derivedLocallyConstantPullback_to_constant f
    have h' := S.congr_map h
    erw [S.map_comp z (l ≫ r), S.map_comp l r, S.map_comp (F.map q) e.hom] at h'
    exact h'
  erw [locallyConstantExtDerivedEquiv_apply M n, locallyConstantExtPullback_hom f n a,
    locallyConstantExtDerivedEquiv_apply N n]
  change (s ≫ (t ≫ d ≫ S.map z) ≫ S.map l) ≫ S.map r =
    e.inv ≫ ShiftedHom.map (a.hom ≫ q⟦(n : ℤ)⟧') F ≫ S.map e.hom
  erw [hm]
  change (s ≫ (t ≫ d ≫ S.map z) ≫ S.map l) ≫ S.map r =
    (s ≫ t) ≫ (d ≫ S.map (F.map q)) ≫ S.map e.hom
  calc
    _ = s ≫ t ≫ d ≫ (S.map z ≫ S.map l ≫ S.map r) := by simp only [Category.assoc]
    _ = s ≫ t ≫ d ≫ (S.map (F.map q) ≫ S.map e.hom) := by rw [ht]
    _ = _ := by simp only [Category.assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtDerivedPullback
