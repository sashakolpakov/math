import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD

/-! # Filtered Complex Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter

noncomputable section

/-! Degree truncation is compatible with the concrete sheaf-complex comparison. -/

open _root_.CategoryTheory Limits ZeroObject

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

section Truncation
variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {K L : CochainComplex C ℕ}

def componentIso (e : K ≅ L) (n : ℕ) : K.X n ≅ L.X n where
  hom := e.hom.f n
  inv := e.inv.f n
  hom_inv_id := congrArg (fun f => f.f n) e.hom_inv_id
  inv_hom_id := congrArg (fun f => f.f n) e.inv_hom_id

def brutalTermIso (e : K ≅ L) (r : ℤ) (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n ≅ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n :=
  if h : r ≤ (n : ℤ) then
    eqToIso (by simp [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, h]) ≪≫ componentIso e n ≪≫
      eqToIso (by simp [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, h])
  else eqToIso (by simp [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, h])

def brutalIso (e : K ≅ L) (r : ℤ) : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r ≅ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r :=
  HomologicalComplex.Hom.isoOfComponents (brutalTermIso e r) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).d i (i + 1) = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d K r i from CochainComplex.of_d _ _ i,
      show (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r).d i (i + 1) = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d L r i from CochainComplex.of_d _ _ i]
    change (brutalTermIso e r i).hom ≫ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d L r i =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d K r i ≫ (brutalTermIso e r (i + 1)).hom
    by_cases h : r ≤ (i : ℤ)
    · have h1 : r ≤ ((i + 1 : ℕ) : ℤ) := by omega
      simp only [brutalTermIso, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d, dite_eq_left h, dite_eq_left h1, Iso.trans_hom,
        eqToIso.hom, componentIso,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [e.hom.comm_assoc]
    · simp only [brutalTermIso, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d, dite_eq_right h, comp_zero, zero_comp])

theorem brutalIso_inclusion (e : K ≅ L) (r : ℤ) :
    (brutalIso e r).hom ≫ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ e.hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (brutalTermIso e r n).hom ≫ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm L r n =
    AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n ≫ e.hom.f n
  by_cases h : r ≤ (n : ℤ)
  · simp only [brutalTermIso, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left h, Iso.trans_hom, eqToIso.hom,
      componentIso, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  · simp only [brutalTermIso, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right h, comp_zero, zero_comp]

end Truncation

section Functors
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

theorem rightComp_map_comp (F : C ⥤ D) {A B C' : C} {T : D}
    (f : A ⟶ B) (g : B ⟶ C') (x : T ⟶ F.obj A) :
    x ≫ F.map (f ≫ g) = (𝟙 _ ≫ (x ≫ F.map f)) ≫ F.map g := by
  simp only [Functor.map_comp, Category.id_comp, Category.assoc]

theorem rightComp_map_iso (F : C ⥤ D) (G : D ⥤ E) {A B C' : C} {T : E}
    (e : A ≅ B) (f : B ⟶ C') (x : T ⟶ G.obj (F.obj B)) :
    (𝟙 _ ≫ ((𝟙 _ ≫ x) ≫ G.map (F.map e.inv))) ≫ G.map (F.map (e.hom ≫ f)) =
      (𝟙 _ ≫ x) ≫ G.map (F.map f) := by
  simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]

end Functors

open _root_.AlgebraicGeometry
variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev NatCohomology (K : CochainComplex (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) ℕ) (n : ℕ) :=
  ShiftedHom ((DerivedCategory.singleFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) 0).obj
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf ℂ X)) ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.derivedFunctor ℂ X).obj K) (n : ℤ)

def natCohomologyEquiv {K L : CochainComplex (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) ℕ}
    (e : K ≅ L) (n : ℕ) : NatCohomology X K n ≃ₗ[ℂ] NatCohomology X L n :=
  Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).mapIso
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.derivedFunctor ℂ X).mapIso e))

def natFiltrationMap (K : CochainComplex (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) ℕ)
    (n : ℕ) (r : ℤ) : NatCohomology X (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) n →ₗ[ℂ] NatCohomology X K n :=
  Linear.rightComp ℂ _
    ((shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).map
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.derivedFunctor ℂ X).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)))

def natFiltration (K : CochainComplex (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) ℕ)
    (n : ℕ) (r : ℤ) : Submodule ℂ (NatCohomology X K n) :=
  LinearMap.range (natFiltrationMap X K n r)

theorem natFiltrationMap_naturality {K L : CochainComplex (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) ℕ}
    (e : K ≅ L) (n : ℕ) (r : ℤ) (x : NatCohomology X (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) n) :
    natCohomologyEquiv X e n (natFiltrationMap X K n r x) =
      natFiltrationMap X L n r (natCohomologyEquiv X (brutalIso e r) n x) := by
  simp only [natCohomologyEquiv, Linear.homCongr_apply, Iso.refl_inv, Category.id_comp,
    Functor.mapIso_hom]
  change (x ≫ _) ≫ _ = (x ≫ _) ≫ _
  simp only [Category.assoc, ← Functor.map_comp, brutalIso_inclusion]

theorem natFiltration_equiv {K L : CochainComplex (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) ℕ}
    (e : K ≅ L) (n : ℕ) (r : ℤ) :
    (natFiltration X K n r).map (natCohomologyEquiv X e n).toLinearMap =
      natFiltration X L n r := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨natCohomologyEquiv X (brutalIso e r) n z,
      (natFiltrationMap_naturality X e n r z).symm⟩
  · rintro ⟨z, rfl⟩
    let x := (natCohomologyEquiv X (brutalIso e r) n).symm z
    refine ⟨natFiltrationMap X K n r x, ⟨x, rfl⟩, ?_⟩
    change natCohomologyEquiv X e n (natFiltrationMap X K n r x) = _
    rw [natFiltrationMap_naturality]
    exact congrArg (natFiltrationMap X L n r)
      ((natCohomologyEquiv X (brutalIso e r) n).apply_symm_apply z)

/-- Identify the two orders of extension and sheafification used by BettiComparison. -/
def extensionCohomologyEquiv (n : ℕ) :
    NatCohomology X (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) n ≃ₗ[ℂ]
      (((DerivedCategory.singleFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) 0).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf ℂ X)) ⟶
        (DerivedCategory.Q.obj (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X))⟦(n : ℤ)⟧) :=
  Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).mapIso
      (DerivedCategory.Q.mapIso (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X).symm))

/-- The inclusion of BettiComparison's degree-truncated sheaf complex into its native integer complex. -/
def filtrationMap66 (n : ℕ) (r : ℤ) :
    NatCohomology X (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r) n →ₗ[ℂ]
      (((DerivedCategory.singleFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) 0).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf ℂ X)) ⟶
        (DerivedCategory.Q.obj (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X))⟦(n : ℤ)⟧) :=
  Linear.rightComp ℂ _
    ((shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).map
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.derivedFunctor ℂ X).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r) ≫
        DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X).inv))

/-- BettiComparison's Hodge filtration, defined by the image of the actual truncated complex. -/
def filtration66 (n : ℕ) (r : ℤ) : Submodule ℂ (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRham X n) :=
  LinearMap.range (filtrationMap66 X n r)

theorem filtrationMap66_extension (n : ℕ) (r : ℤ)
    (x : NatCohomology X (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r) n) :
    filtrationMap66 X n r x = extensionCohomologyEquiv X n
      (natFiltrationMap X (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) n r x) := by
  exact rightComp_map_comp (shiftFunctor _ (n : ℤ))
    ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.derivedFunctor ℂ X).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r))
    (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X).inv) x

theorem cohomologyEquiv_extension (n : ℕ)
    (x : NatCohomology X (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) n) :
    SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n (extensionCohomologyEquiv X n x) =
      natCohomologyEquiv X (SheafFormsAdapter.FormsAdapter.sheafComplexIso X) n x := by
  exact rightComp_map_iso DerivedCategory.Q (shiftFunctor _ (n : ℤ))
    (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X)
    ((ComplexShape.embeddingUpNat.extendFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)).map
      (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom) x

theorem filtrationMap66_comparison (n : ℕ) (r : ℤ)
    (x : NatCohomology X (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r) n) :
    SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n (filtrationMap66 X n r x) =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap ℂ X n r (natCohomologyEquiv X (brutalIso (SheafFormsAdapter.FormsAdapter.sheafComplexIso X) r) n x) := by
  rw [filtrationMap66_extension, cohomologyEquiv_extension]
  exact natFiltrationMap_naturality X (SheafFormsAdapter.FormsAdapter.sheafComplexIso X) n r x

/-- The direct form adapter preserves every step of the genuine Hodge filtration. -/
theorem cohomologyEquiv_filtration (n : ℕ) (r : ℤ) :
    (filtration66 X n r).map (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ X n r := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨natCohomologyEquiv X (brutalIso (SheafFormsAdapter.FormsAdapter.sheafComplexIso X) r) n z,
      (filtrationMap66_comparison X n r z).symm⟩
  · rintro ⟨z, rfl⟩
    let x := (natCohomologyEquiv X (brutalIso (SheafFormsAdapter.FormsAdapter.sheafComplexIso X) r) n).symm z
    refine ⟨filtrationMap66 X n r x, ⟨x, rfl⟩, ?_⟩
    change SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n (filtrationMap66 X n r x) = _
    rw [filtrationMap66_comparison]
    exact congrArg (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap ℂ X n r)
      ((natCohomologyEquiv X (brutalIso (SheafFormsAdapter.FormsAdapter.sheafComplexIso X) r) n).apply_symm_apply z)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter
