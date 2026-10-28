import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi
import Mathlib.Algebra.Homology.Single

/-! # Single Complex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleComplex.SingleComplexAssembly

noncomputable section

/-! # Assembly commutes with complexes concentrated in a single degree -/

open _root_.CategoryTheory Limits

universe u v w z

variable {C : Type u} [Category.{v} C] {V : Type w} [Category.{z} V]
  [Preadditive V] [HasZeroObject V] (F : C ⥤ V)

local notation "c" => ComplexShape.up ℕ
local notation "S" => CochainComplex.single₀ V
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex c (F ⋙ S)
local notation "L" => Functor.obj (CochainComplex.single₀ (C ⥤ V)) F

def degreeZeroIso : (K).X 0 ≅ F :=
  Functor.associator F S (HomologicalComplex.eval V c 0) ≪≫
    Functor.isoWhiskerLeft F (HomologicalComplex.singleCompEvalIsoSelf V c 0) ≪≫
    Functor.rightUnitor F

def componentIso (n : ℕ) : (K).X n ≅ (L).X n := by
  by_cases hn : n = 0
  · subst n
    exact degreeZeroIso F ≪≫ (HomologicalComplex.singleObjXSelf c 0 F).symm
  · exact (Functor.isZero ((K).X n)
      (fun t => HomologicalComplex.isZero_single_obj_X c 0 (F.obj t) n hn)).iso
        (HomologicalComplex.isZero_single_obj_X c 0 F n hn)

def iso : K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents (componentIso F) (by
    intro i j _
    have hK : (K).d i j = 0 := by
      apply NatTrans.ext
      funext t
      exact HomologicalComplex.single_obj_d c 0 (F.obj t) i j
    simp only [hK, HomologicalComplex.single_obj_d, comp_zero, zero_comp])

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleComplex.SingleComplexAssembly
