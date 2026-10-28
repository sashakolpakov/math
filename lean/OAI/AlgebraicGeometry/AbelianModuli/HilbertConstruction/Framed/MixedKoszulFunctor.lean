import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.LineBundleKoszulStep
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleKoszulComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.FiniteTerms

/-! # Mixed Koszul Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulFunctor

noncomputable section

/-! A scalar-compatible additive functor takes a mixed Koszul complex
to the scalar Koszul complex of its actual frame coordinates. Frames
are required only for the finitely many bundles occurring in the list. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def framedMixedKoszulFunctorIso (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
    (φ : Γ(X, ⊤) →+* R)
    (hF : ∀ (M : X.Modules) (r : Γ(X, ⊤)),
      F.map (Global.ModuleScalars.globalModuleScalar M r) = φ r • 𝟙 (F.obj M))
    (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (ρ : LineBundleKoszulComplex.LineBundleSection X → R)
    (hframe : ∀ b ∈ bs, ∃ e : b.1.sheaf ≅ Line.Bundles.structureModule X,
      φ (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ e.hom)) = ρ b) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs)) ≅
      ScalarKoszul.KoszulComplex.scalarKoszulComplex (F.obj M) (bs.map ρ) := by
  have : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  induction bs with
  | nil => exact (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M
  | cons b bs ih =>
    let e := Classical.choose (hframe b (by simp))
    have he := Classical.choose_spec (hframe b (by simp))
    let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs
    let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
    let D := ScalarKoszul.KoszulComplex.scalarKoszulComplex (F.obj M) (bs.map ρ)
    let a : FC ≅ D := ih (fun b hb => hframe b (List.mem_cons_of_mem _ hb))
    let r := Frame.Coordinates.structureModuleEndValue X (b.2 ≫ e.hom)
    have hscalar : (F.mapHomologicalComplex (.up ℤ)).map (LineBundleKoszulStep.globalScalarComplexMap r C) =
        ρ b • 𝟙 FC := by
      apply HomologicalComplex.Hom.ext
      funext i
      change F.map (Global.ModuleScalars.globalModuleScalar (C.X i) r) = ρ b • 𝟙 (F.obj (C.X i))
      rw [hF, he]
    let e₁ := (F.mapHomologicalComplex (.up ℤ)).mapIso (LineBundleKoszulStep.framedLineBundleKoszulStepIso b.1 b.2 e C)
    let e₂ := CochainComplex.mappingCone.mapHomologicalComplexIso (LineBundleKoszulStep.globalScalarComplexMap r C) F
    let e₃ := eqToIso (congrArg (fun f : FC ⟶ FC => CochainComplex.mappingCone f) hscalar)
    let e₄ := HomologicalComplex.homotopyCofiber.mapArrowIso (ρ b • 𝟙 FC) (ρ b • 𝟙 D)
      (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
      (Arrow.isoMk a a (by
        change a.hom ≫ (ρ b • 𝟙 D) = (ρ b • 𝟙 FC) ≫ a.hom
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]))
    exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

theorem framedMixedKoszulFunctor_finite_free (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
    (φ : Γ(X, ⊤) →+* R)
    (hF : ∀ (M : X.Modules) (r : Γ(X, ⊤)),
      F.map (Global.ModuleScalars.globalModuleScalar M r) = φ r • 𝟙 (F.obj M))
    (M : X.Modules) [Module.Finite R (F.obj M)] [Module.Free R (F.obj M)]
    (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (ρ : LineBundleKoszulComplex.LineBundleSection X → R)
    (hframe : ∀ b ∈ bs, ∃ e : b.1.sheaf ≅ Line.Bundles.structureModule X,
      φ (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ e.hom)) = ρ b) :
    ∀ i, Module.Finite R (F.obj ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i)) ∧
      Module.Free R (F.obj ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i)) := by
  let e := framedMixedKoszulFunctorIso F φ hF M bs ρ hframe
  intro i
  have hff := ScalarKoszul.FiniteTerms.scalarKoszulComplex_finite_free (F.obj M) (bs.map ρ) i
  have : Module.Finite R ((ScalarKoszul.KoszulComplex.scalarKoszulComplex (F.obj M) (bs.map ρ)).X i) := hff.1
  have : Module.Free R ((ScalarKoszul.KoszulComplex.scalarKoszulComplex (F.obj M) (bs.map ρ)).X i) := hff.2
  let ei : ((ScalarKoszul.KoszulComplex.scalarKoszulComplex (F.obj M) (bs.map ρ)).X i) ≃ₗ[R]
      F.obj ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i) :=
    ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i).mapIso e).symm.toLinearEquiv
  exact ⟨Module.Finite.equiv ei, Module.Free.of_equiv ei⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulFunctor
