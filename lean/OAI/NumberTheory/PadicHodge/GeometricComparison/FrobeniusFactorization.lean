import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FieldFrobeniusGeometry

/-! # Frobenius Factorization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusFactorization.FiniteFieldFrobeniusGeometry

noncomputable section

/-! The actual Completion geometric q-power morphism factors as absolute q-power followed by the actual IntegralComparison inverse-field Frobenius automorphism. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

variable (k : Type) [Field k] [Fintype k] (A : Over (Spec (CommRingCat.of k)))

def geometricFiberBaseMap : k →+* Γ(AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A, ⊤) :=
  (pullback.fst A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase k)).appTop.hom.comp (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.varietyBaseMap k A)

def absoluteOnGeometricFiber : AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A ⟶ AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A :=
  AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A) (geometricFiberBaseMap k A)

variable (p a : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ a)

theorem geometricFrobenius_factorization :
    AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricSchemeFrobenius k A = absoluteOnGeometricFiber k A ≫
      (IntegralComparison.Frobenius.Geometry.geometricFiberIso A.hom (IntegralComparison.Frobenius.Geometry.geometricFrobenius p a k hcard)).hom := by
  let Y := AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A
  let f : Y ⟶ A.left := pullback.fst A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase k)
  let g : Y ⟶ Spec (CommRingCat.of (AlgebraicClosure k)) := pullback.snd A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase k)
  let κS := AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.varietyBaseMap k (Over.mk (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase k))
  let Q := AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k (Spec (CommRingCat.of (AlgebraicClosure k))) κS
  let s := IntegralComparison.Frobenius.Geometry.scalarSchemeIso (IntegralComparison.Frobenius.Geometry.geometricFrobenius p a k hcard)
  let t : Y ≅ Y := IntegralComparison.Frobenius.Geometry.geometricFiberIso A.hom (IntegralComparison.Frobenius.Geometry.geometricFrobenius p a k hcard)
  have ht_f : t.hom ≫ f = f := IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_fst A.hom (IntegralComparison.Frobenius.Geometry.geometricFrobenius p a k hcard)
  have ht_g : t.hom ≫ g = g ≫ s.hom := IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_snd A.hom (IntegralComparison.Frobenius.Geometry.geometricFrobenius p a k hcard)
  have hf : absoluteOnGeometricFiber k A ≫ f = f ≫ (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A).left :=
    AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius_naturality k Y (geometricFiberBaseMap k A) (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.varietyBaseMap k A) f
  have hg : absoluteOnGeometricFiber k A ≫ g = g ≫ Q :=
    AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius_naturality k Y (geometricFiberBaseMap k A) κS g
  have hQ : Q ≫ s.hom = 𝟙 _ := by
    rw [show Q = (IntegralComparison.Frobenius.Geometry.scalarSchemeIso (IntegralComparison.Frobenius.Geometry.arithmeticFrobenius p a k hcard)).hom from Finite.FieldFrobeniusGeometry.FiniteFieldFrobeniusGeometry.scalarFrobenius_eq p a k hcard κS]
    exact (IntegralComparison.Frobenius.Geometry.scalarSchemeIso (IntegralComparison.Frobenius.Geometry.arithmeticFrobenius p a k hcard)).hom_inv_id
  change AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricSchemeFrobenius k A = absoluteOnGeometricFiber k A ≫ t.hom
  apply pullback.hom_ext
  · calc
      _ = f ≫ (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A).left := AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberMap_fst k (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A)
      _ = absoluteOnGeometricFiber k A ≫ f := hf.symm
      _ = _ := (congrArg (fun z => absoluteOnGeometricFiber k A ≫ z) ht_f).symm.trans
        (Category.assoc (absoluteOnGeometricFiber k A) t.hom f).symm
  · calc
      _ = g := AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberMap_snd k (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A)
      _ = (g ≫ Q) ≫ s.hom := by rw [Category.assoc, hQ, Category.comp_id]
      _ = (absoluteOnGeometricFiber k A ≫ g) ≫ s.hom := congrArg (fun z => z ≫ s.hom) hg.symm
      _ = _ := (Category.assoc (absoluteOnGeometricFiber k A) g s.hom).trans
        ((congrArg (fun z => absoluteOnGeometricFiber k A ≫ z) ht_g).symm.trans
          (Category.assoc (absoluteOnGeometricFiber k A) t.hom g).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusFactorization.FiniteFieldFrobeniusGeometry
