import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcPoincareRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedFactor

/-! # Fpqc Mixed Poincare Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcMixedPoincareRecovery.Construction

noncomputable section

/-! Recovery of the actual line on the simultaneous abelian-dual
product gives full native dual data across an fpqc base extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedFactor

theorem lineClass_pullback_iso_injective {X Y : Scheme.{0}} (e : X ≅ Y) :
    Function.Injective (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom) := by
  intro c d h
  have hi (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y) :
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom q) = q := by
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, e.inv_hom_id, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  exact (hi c).symm.trans ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv) h).trans (hi d))

variable {S Y : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : Y ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme) [IsMonHom eA.hom]
    (E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (eD : D.abelian.scheme ≅ (E.pullback u).scheme)

def recoveredDualParameter : (Over.map u).obj D.abelian.scheme ⟶ E.scheme :=
  Over.homMk (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E.scheme eD)
    (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap_base u D.abelian.scheme E.scheme eD)

variable (J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (E.scheme ⊗ B.scheme).left)

omit [IsMonHom eA.hom] in
set_option backward.isDefEq.respectTransparency false in
theorem mixedPoincare_recovery_iff :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (recoveredDualParameter D u E eD ▷ B.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA) := by
  let c := AbelianModuli.ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincareComparison D B u eA
  let q := recoveredDualParameter D u E eD
  have hfactor := AbelianModuli.ReferenceFamily.PoincareFixedFactor.fixedFamilyPoincareComparison_factor D B u eA E.scheme eD q rfl
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.hom
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) := by
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hfactor]
  constructor
  · intro h
    apply lineClass_pullback_iso_injective c
    exact he.trans (h.trans (AbelianModuli.ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincare_recovery_class D B u eA).symm)
  · intro h
    exact he.symm.trans ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.hom) h).trans
      (AbelianModuli.ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincare_recovery_class D B u eA))

variable (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme)
    [Flat u] [Surjective u] [QuasiCompact u] [IsMonHom eD.hom]
    (hr : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

def fpqcMixedDescendedDualData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B :=
  FpqcPoincareRecovery.Construction.fpqcDualDataOfRecoveredPoincare D B hB u eA E eD (recoveredDualParameter D u E eD) rfl J
    ((mixedPoincare_recovery_iff D B u eA E eD J).mp hr)

theorem fpqcMixedDescendedDualData_abelian :
    (fpqcMixedDescendedDualData D B u eA E eD J hB hr).abelian = E := rfl

theorem fpqcMixedDescendedDualData_recovery :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (fpqcMixedDescendedDualData D B u eA E eD J hB hr).poincare) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare :=
  (mixedPoincare_recovery_iff D B u eA E eD _).mpr
    (FpqcPoincareRecovery.Construction.fpqcDualDataOfRecoveredPoincare_recovery D B hB u eA E eD (recoveredDualParameter D u E eD)
      rfl J ((mixedPoincare_recovery_iff D B u eA E eD J).mp hr))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcMixedPoincareRecovery.Construction
