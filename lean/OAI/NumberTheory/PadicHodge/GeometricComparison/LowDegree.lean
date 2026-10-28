import OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroQuotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendShort
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionFinite
import OAI.NumberTheory.PadicHodge.GeometricComparison.TriangleFinitenessFinite
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Low Degree -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LowDegree.LowDegreeHypercohomologyFinite

noncomputable section

/-! Finite H-one of the zero term and finite global one-forms bound actual de Rham H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated Opposite

variable (R : Type) [CommRing R] [IsNoetherianRing R] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _
local instance : HasExt.{1} V := HasExt.standard _

theorem finite (K : CochainComplex V ℕ)
    [Module.Finite R ((K.X 1).obj.obj (op ⊤))]
    [Module.Finite R (Abelian.Ext.{1} A (K.X 0) 1)] :
    Module.Finite R ((DerivedCategory.singleFunctor V 0).obj A ⟶
      (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) := by
  let S := (First.ZeroQuotient.FirstZeroComplex.quotientSequence K).map (ComplexShape.embeddingUpNat.extendFunctor V)
  have hS : S.ShortExact := ExtendShort.ExtendShortExact.shortExact _ _ (First.ZeroQuotient.FirstZeroComplex.quotient_shortExact K)
  let T := (shiftFunctor (Triangle (DerivedCategory V)) (1 : ℤ)).obj
    (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (DerivedCategory V) :=
    Triangle.shift_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) 1
  let L : CochainComplex V ℤ :=
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 1).extend ComplexShape.embeddingUpNat
  let : L.IsStrictlyGE 1 := TruncationBoundsGE.TruncationBounds.extended_isStrictlyGE K 1
  let : (L⟦(1 : ℤ)⟧).IsStrictlyGE 0 := L.isStrictlyGE_shift 1 1 0 rfl
  let : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1).f 1) := by
    change IsIso (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 1 1)
    rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left (by norm_num)]
    infer_instance
  let e₁ : (L⟦(1 : ℤ)⟧).X 0 ≅ K.X 1 :=
    L.shiftFunctorObjXIso 1 0 1 rfl ≪≫
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 1).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl ≪≫
        asIso ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1).f 1)
  let sections := (sheafSections (Opens.grothendieckTopology X) (ModuleCat R)).obj (op ⊤)
  let : Module.Finite R (sections.obj (K.X 1)) :=
    inferInstanceAs (Module.Finite R ((K.X 1).obj.obj (op ⊤)))
  let : Module.Finite R (((L⟦(1 : ℤ)⟧).X 0).obj.obj (op ⊤)) :=
    Module.Finite.equiv ((sections.mapIso e₁).toLinearEquiv.symm)
  let : Module.Finite R ((DerivedCategory.singleFunctor V 0).obj A ⟶
      (shiftFunctor (CochainComplex V ℤ) (1 : ℤ) ⋙ DerivedCategory.Q).obj L) :=
    ConnectiveSectionFinite.ConnectiveSectionFiniteness.finite R X (L⟦(1 : ℤ)⟧)
  let h₁ := Linear.homCongr R (Iso.refl ((DerivedCategory.singleFunctor V 0).obj A))
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app L)
  let : Module.Finite R ((DerivedCategory.singleFunctor V 0).obj A ⟶ T.obj₁) :=
    Module.Finite.equiv h₁
  let : Module.Finite R ((DerivedCategory.singleFunctor V 0).obj A ⟶
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor V 0).obj (K.X 0)))⟦(1 : ℤ)⟧) :=
    Module.Finite.equiv (Abelian.Ext.homLinearEquiv (R := R))
  let e₀ : ((First.ZeroQuotient.FirstZeroComplex.complex K).extend ComplexShape.embeddingUpNat) ≅
      (CochainComplex.singleFunctor V 0).obj (K.X 0) :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (K.X 0) 0 0 rfl
  let h₀ := Linear.homCongr R (Iso.refl ((DerivedCategory.singleFunctor V 0).obj A))
    ((shiftFunctor (DerivedCategory V) (1 : ℤ)).mapIso (DerivedCategory.Q.mapIso e₀))
  let : Module.Finite R ((DerivedCategory.singleFunctor V 0).obj A ⟶ T.obj₃) :=
    Module.Finite.equiv h₀.symm
  exact TriangleFinitenessFinite.TriangleFiniteness.finite R T hT ((DerivedCategory.singleFunctor V 0).obj A)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LowDegree.LowDegreeHypercohomologyFinite
