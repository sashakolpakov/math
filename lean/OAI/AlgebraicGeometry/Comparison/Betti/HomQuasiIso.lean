import OAI.AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex
import OAI.AlgebraicGeometry.Comparison.Betti.MappingConeQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.MappingConeExtAcyclic

/-! # Hom Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomQuasiIso.Ext

noncomputable section

/-! Hom preserves quasi-isomorphisms between bounded-below complexes of Ext-acyclic objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Opposite _root_.HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) {K L : CochainComplex C ℤ} (f : K ⟶ L)

theorem integerHomComplex_map_quasiIso (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n]
    [QuasiIso f]
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A (L.X p) (q + 1))) :
    QuasiIso (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map f) := by
  let M := CochainComplex.mappingCone f
  have : M.IsStrictlyGE (n - 1) := MappingConeExtAcyclic.mappingCone_isStrictlyGE f n
  have hM : M.Acyclic := (MappingConeQuasiIso.Ext.quasiIso_iff_mappingCone_acyclic f).mp inferInstance
  have hExt := MappingConeExtAcyclic.mappingCone_termExt_acyclic f A hK hL
  have hHom := IntegerAcyclicHomComplex.Ext.integerHomComplex_acyclic A M (n - 1) hM hExt
  rw [MappingConeQuasiIso.Ext.quasiIso_iff_mappingCone_acyclic]
  intro p
  exact (hHom p).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (preadditiveCoyoneda.obj (op A)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomQuasiIso.Ext
