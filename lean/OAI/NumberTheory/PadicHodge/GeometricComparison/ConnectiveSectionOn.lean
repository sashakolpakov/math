import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionCycle

/-! # Connective Section On -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionOn.ConnectiveSectionNaturality

/-! The degree-zero derived-section calculation respects maps of connective complexes. -/

open _root_.CategoryTheory Opposite

variable (R : Type) [CommRing R] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

theorem on_cochainMap (K : CochainComplex V ℤ) [K.IsStrictlyGE 0]
    (a : (CochainComplex.singleFunctor V 0).obj A ⟶ K) :
    (ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X K (DerivedCategory.Q.map a)).val =
      ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0)
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ a.f 0) := by
  change (ConnectiveSectionCycle.ConnectiveSectionKernel.cycleEquiv R X K
    (SingleMap.SingleMapCycles.equiv R A K 0
      ((ConnectiveDerivedEquiv.ConnectiveDerivedEquivalence.equiv R 0).symm (DerivedCategory.Q.map a)))).val = _
  change (ConnectiveSectionCycle.ConnectiveSectionKernel.cycleEquiv R X K
    (SingleMap.SingleMapCycles.equiv R A K 0
      ((ConnectiveDerivedEquiv.ConnectiveDerivedEquivalence.equiv R 0).symm (ConnectiveDerivedEquiv.ConnectiveDerivedEquivalence.equiv R 0 a)))).val = _
  erw [LinearEquiv.symm_apply_apply]
  rfl

theorem naturality (K L : CochainComplex V ℤ) [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (f : K ⟶ L) (a : (DerivedCategory.singleFunctor V 0).obj A ⟶ DerivedCategory.Q.obj K) :
    (ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X L (a ≫ DerivedCategory.Q.map f)).val =
      (f.f 0).hom.app (op ⊤) (ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X K a).val := by
  obtain ⟨b, rfl⟩ := ConnectiveDerivedIs.ConnectiveDerivedMaps.surjective 0 (X := (CochainComplex.singleFunctor V 0).obj A) a
  erw [← DerivedCategory.Q.map_comp, on_cochainMap, on_cochainMap]
  change ConstantSheaf.ConstantSheafSections.linearEquiv R X (L.X 0)
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ b.f 0 ≫ f.f 0) = _
  erw [← Category.assoc, ConstantSheaf.ConstantSheafSections.naturality]

end NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionOn.ConnectiveSectionNaturality

namespace NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionOn.ConnectiveSectionSurjectivity

/-! Surjective degree-zero sections lift derived degree-zero sections when the source global differential is zero. -/

open _root_.CategoryTheory Opposite

variable (R : Type) [CommRing R] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

theorem surjective (K L : CochainComplex V ℤ) [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (f : K ⟶ L)
    (hf : Function.Surjective ((f.f 0).hom.app (op ⊤)))
    (hd : ∀ x : (K.X 0).obj.obj (op ⊤), (K.d 0 1).hom.app (op ⊤) x = 0) :
    Function.Surjective (fun a : (DerivedCategory.singleFunctor V 0).obj A ⟶ DerivedCategory.Q.obj K =>
      a ≫ DerivedCategory.Q.map f) := by
  intro a
  obtain ⟨x, hx⟩ := hf (ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X L a).val
  let z : ConnectiveSectionCycle.ConnectiveSectionKernel.sectionKernel R X K := ⟨x, hd x⟩
  refine ⟨(ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X K).symm z, ?_⟩
  apply (ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X L).injective
  apply Subtype.ext
  rw [ConnectiveSectionNaturality.naturality, LinearEquiv.apply_symm_apply]
  exact hx

end NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionOn.ConnectiveSectionSurjectivity

end

end OAI
