import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomComplex
import OAI.AlgebraicGeometry.Comparison.Betti.RestrictionAcyclicity
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Integer Acyclic Hom Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext

noncomputable section

/-! Hom preserves acyclic bounded-below integer complexes of Ext-acyclic objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) (K : CochainComplex C ℤ)

def integerHomComplex : CochainComplex AddCommGrpCat.{v} ℤ :=
  ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj K

theorem integerHomComplex_acyclic (n : ℤ) [K.IsStrictlyGE n] (hK : K.Acyclic)
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) :
    (integerHomComplex A K).Acyclic := by
  let e := ComplexShape.embeddingUpIntGE n
  let J := K.restriction e
  let L := integerHomComplex A K
  have hJ : J.Acyclic := RestrictionAcyclicity.Ext.supportedRestriction_acyclic K e hK
  have hJExt (p q : ℕ) : Subsingleton (Ext A (J.X p) (q + 1)) := hExt (e.f p) q
  have hm := Betti.Acyclic.HomComplex.Ext.nonnegativeHomComplex_acyclic A J hJ hJExt
  have hL : (L.restriction e).Acyclic := hm
  have : L.IsStrictlySupported e :=
    inferInstanceAs
      ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj K).IsStrictlySupported
        (ComplexShape.embeddingUpIntGE n))
  exact RestrictionAcyclicity.Ext.acyclic_of_supportedRestriction L e hL

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext
