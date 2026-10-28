import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SourceComponent
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.IntrinsicTotalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

/-! # Global Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.GlobalEdge

noncomputable section

/-! The mixed Hom-total source edge is the literal global-section
Čech edge, including the canonical coefficient lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u z
variable {C : Type u} [Category.{0} C] [HasBinaryProducts C]
  {ι : Type} [Finite ι] (F : ι → C) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (K : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ)

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{max u z} R) :=
  fun T => (ModuleCat.hasColimitsOfSize.{max u z,u,0,0} R).has_colimits_of_shape (Discrete T)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.complex J R F
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation J R F

def nativeEdge : Global.SectionCechEdge.globalComplex R (IntrinsicTotalCoordinates.Intrinsic.presheafComplex.{u,0} R J K) ⟶ ((IntrinsicTotalCoordinates.Intrinsic.bicomplex.{u,0} F R J K)).total (.up ℕ) :=
  Global.SectionCechEdge.edge R F (IntrinsicTotalCoordinates.Intrinsic.presheafComplex.{u,0} R J K)

def edge : IntegralComparison.Sheaf.PresheafSectionComplex.complex.{u,0,u,z} R J K ⟶
    (ExtCoefficientEdge.bicomplex.{u,0,z} F R J K).total (.up ℕ) :=
  (((ModuleCat.uliftFunctor.{z,u} R)).mapHomologicalComplex (.up ℕ)).map (nativeEdge F R J K) ≫
    (IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K).inv

private theorem component_square {A : Type*} [Category A]
    {V B C D E F G : A}
    (e : V ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : B ⟶ F) (i : F ⟶ D) (j : F ⟶ E)
    (s : V ⟶ G) (t : G ⟶ F) (l : G ⟶ E)
    (h₁ : a ≫ b = d ≫ i) (h₂ : i ≫ c = j)
    (h₃ : e ≫ d = s ≫ t) (h₄ : l = t ≫ j) :
    ((e ≫ a) ≫ b) ≫ c = s ≫ l := by
  simp only [Category.assoc]
  rw [← Category.assoc a b c, h₁, Category.assoc, h₂,
    ← Category.assoc e d j, h₃, Category.assoc, ← h₄]

private theorem complexHom_ext {C : Type*} [Category C] [HasZeroMorphisms C]
    {K L : CochainComplex C ℕ} (f g : K ⟶ L)
    (h : ∀ q, f.f q = g.f q) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact h q

private theorem coordinates_component (q : ℕ) :
    ((ResolutionHom.Total.edge R S ε K ≫
    (ExtCoefficientEdge.totalIso.{u,0,z} F R J K).hom) ≫
      (IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K).hom).f q =
    (    (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u,0,u,z} R J K).hom ≫
      ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
        (nativeEdge F R J K)).f q := by
  change ((ResolutionHom.Total.component R S ε K q ≫
    (ResolutionHom.Bicomplex.bicomplex R S K).ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map
        (ExtBicomplex.bicomplexIso.{u,0,z} F R J K).hom (.up ℕ)).f q) ≫
        AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent (ModuleCat.uliftFunctor.{z,u} R)
          (IntrinsicTotalCoordinates.Intrinsic.bicomplex.{u,0} F R J K) q =
    (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u,0,u,z} R J K).hom.f q ≫
      (ModuleCat.uliftFunctor.{z,u} R).map ((nativeEdge F R J K).f q)
  have ht := HomologicalComplex₂.ιTotal_map
    (K := ResolutionHom.Bicomplex.bicomplex R S K)
    (L := ExtCoefficientEdge.bicomplex.{u,0,z} F R J K)
    (φ := (ExtBicomplex.bicomplexIso.{u,0,z} F R J K).hom)
    (c₁₂ := .up ℕ) q 0 q rfl
  have hc := AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent (ModuleCat.uliftFunctor.{z,u} R)
    (IntrinsicTotalCoordinates.Intrinsic.bicomplex.{u,0} F R J K) q 0 q rfl
  have hs := SourceComponent.square.{u,z} F R J (K.X q)
  have he := Global.SectionCechEdge.component R F
    (IntrinsicTotalCoordinates.Intrinsic.presheafComplex.{u,0} R J K) q
  have he' := (congrArg (ModuleCat.uliftFunctor.{z,u} R).map he).trans
    ((ModuleCat.uliftFunctor.{z,u} R).map_comp _ _)
  exact component_square _ _ _ _ _ _ _ _ _ _ ht hc hs he'

theorem coordinates : (ResolutionHom.Total.edge R S ε K ≫
    (ExtCoefficientEdge.totalIso.{u,0,z} F R J K).hom) ≫
      (IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K).hom =
    (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u,0,u,z} R J K).hom ≫
      ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
        (nativeEdge F R J K) := by
  exact complexHom_ext _ _ (coordinates_component F R J K)

private theorem cancel_coordinates {A : Type*} [Category A]
    {V W Z T : A} (f : V ⟶ W) (e : W ≅ Z) (g : V ⟶ T) (h : T ⟶ Z)
    (w : f ≫ e.hom = g ≫ h) : f = g ≫ h ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using w

theorem square : ResolutionHom.Total.edge R S ε K ≫
    (ExtCoefficientEdge.totalIso.{u,0,z} F R J K).hom =
      (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u,0,u,z} R J K).hom ≫ edge F R J K :=
  cancel_coordinates _ (IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K) _ _
    (coordinates F R J K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.GlobalEdge
