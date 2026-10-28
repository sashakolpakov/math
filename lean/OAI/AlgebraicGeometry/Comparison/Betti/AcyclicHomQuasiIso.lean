import OAI.AlgebraicGeometry.Comparison.Betti.HomQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.ExtendedAcyclicCocycles
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueNatQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.LinearHomForget

/-! # Acyclic Hom Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AcyclicHomQuasiIso.Ext

noncomputable section

/-! Hom preserves quasi-isomorphisms between actual nonnegative
complexes of Ext-acyclic objects, with complex-linear coefficients as well. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Opposite _root_.HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) {K L : CochainComplex C ℕ} (f : K ⟶ L)

theorem nonnegativeHomComplex_map_quasiIso [QuasiIso f]
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A (L.X p) (q + 1))) :
    QuasiIso (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map f) := by
  let e := ComplexShape.embeddingUpIntGE 0
  let H := preadditiveCoyoneda.obj (op A)
  have hfe : QuasiIso (HomologicalComplex.extendMap f e) :=
    (HomologicalComplex.quasiIso_extendMap_iff f e).mpr inferInstance
  have he := HomQuasiIso.Ext.integerHomComplex_map_quasiIso A (HomologicalComplex.extendMap f e) 0
    (ExtendedAcyclicCocycles.Ext.extended_term_ext_vanish A K hK) (ExtendedAcyclicCocycles.Ext.extended_term_ext_vanish A L hL)
  let a := Complex.Extension.mapExtendIso H e K
  let b := Complex.Extension.mapExtendIso H e L
  let ei : Arrow.mk ((H.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap f e)) ≅
      Arrow.mk (HomologicalComplex.extendMap ((H.mapHomologicalComplex (.up ℕ)).map f) e) :=
    Arrow.isoMk a b (Complex.Extension.mapExtendIso_naturality H e f).symm
  apply (HomologicalComplex.quasiIso_extendMap_iff _ e).mp
  exact (quasiIso_iff_of_arrow_mk_iso _ _ ei).mp he

theorem nonnegativeLinearHomComplex_map_quasiIso {R : Type v} [CommRing R] [Linear R C]
    [QuasiIso f] (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A (L.X p) (q + 1))) :
    QuasiIso ((((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℕ)).map f) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).mp
  exact nonnegativeHomComplex_map_quasiIso A f hK hL

end

end OAI.AlgebraicGeometry.Comparison.Betti.AcyclicHomQuasiIso.Ext
