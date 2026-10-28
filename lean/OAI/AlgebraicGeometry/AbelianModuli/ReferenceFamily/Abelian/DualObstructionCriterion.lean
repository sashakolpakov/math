import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalObstructionLinear

/-! # Dual Obstruction Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualObstructionCriterion

noncomputable section

/-! For an actual proper smooth connected commutative group family
over dual numbers, zero native obstruction gives an actual normalized
group product compatible with every group endomorphism of the family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (X : Over (Spec (.of (DualNumber ℂ)))) [GrpObj X] [IsCommMonObj X]
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]

local instance abelianDualFiber_smooth : Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom :=
  inferInstanceAs (Smooth (pullback.snd X.hom (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)))

local instance abelianDualFiber_proper : IsProper (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)))

local instance abelianDualFiber_connected : GeometricallyConnected (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd X.hom (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)))

local instance abelianDualFiber_integral : IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left :=
  Picard.Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)

local instance abelianDualH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)

variable (U : X.left.AffineOpenCover)

theorem abelianDualObstruction_zero_iff_groupProduct :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear X U = 0 ↔
    ∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e ∧ IsMonHom e.hom := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := (Dual.ConormalObstructionLinear.dualConormalObstructionLinear_zero_iff_product X U).mp h
    exact NormalizedDual.ProductGroupIso.exists_normalized_groupDualProduct X e he
  · rintro ⟨e, he, _⟩
    exact (Dual.ConormalObstructionLinear.dualConormalObstructionLinear_zero_iff_product X U).mpr ⟨e, he⟩

theorem abelianDualObstruction_zero_equivariantProduct (h : Dual.ConormalObstructionLinear.dualConormalObstructionLinear X U = 0) :
    ∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e ∧ IsMonHom e.hom ∧
      ∀ u : X ⟶ X, IsMonHom u →
        u ≫ e.hom = e.hom ≫ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).map ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).map u) := by
  obtain ⟨e, he, hmon⟩ := (abelianDualObstruction_zero_iff_groupProduct X U).mp h
  have := hmon
  refine ⟨e, he, hmon, ?_⟩
  intro u hu
  have := hu
  exact NormalizedDual.ProductAction.normalizedGroupDualProduct_endomorphism X e he u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualObstructionCriterion
