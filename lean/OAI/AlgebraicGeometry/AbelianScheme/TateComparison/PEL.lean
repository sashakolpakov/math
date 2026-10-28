import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # PEL -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PEL

noncomputable section

/-!
Actual candidate PEL families for the TateComparison interface. The abelian and dual
schemes, Poincare bundle, finite flat isogeny, full marking, and integral
endomorphism action are geometric objects. Positivity, polarization type,
and Rosati compatibility are separate explicit predicates. No moduli
representation, isogeny classification, or Albanese action is a field.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable (R : Type u) [CommRing R]

/-- Candidate polarized endomorphism-and-level data over an actual base. -/
structure PELFamilyData (g N : ℕ) (S : Scheme.{u}) where
  abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S
  dual : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData abelian
  polarizationMap : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny abelian dual.abelian
  marking : abelian.FullLevel N
  action : R →+* End.IntegralEnd abelian.scheme

namespace PELFamilyData

variable {R} {g N : ℕ} {S T : Scheme.{u}}

/-- Poincare pullback identifies the actual dual of a group endomorphism. -/
def IsPoincareDual (D : PELFamilyData R g N S)
    (a : End.IntegralEnd D.abelian.scheme) (b : End.IntegralEnd D.dual.abelian.scheme) : Prop :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (𝟙 D.dual.abelian.scheme ⊗ₘ End.endSchemeMap D.abelian.scheme a).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.dual.poincare) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (End.endSchemeMap D.dual.abelian.scheme b ⊗ₘ 𝟙 D.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.dual.poincare)

/-- The Rosati adjoint of b is the prescribed conjugate c(b). Existence
of an integral adjoint is part of the usual PEL condition, not an assumption
of Hecke realization or of any desired compatibility of correspondences. -/
def IsRosatiCompatible (D : PELFamilyData R g N S) (c : R →+* R) : Prop :=
  ∀ b : R, ∃ bd : End.IntegralEnd D.dual.abelian.scheme,
    D.IsPoincareDual (D.action b) bd ∧
      D.polarizationMap.hom ≫ End.endSchemeMap D.dual.abelian.scheme bd =
        End.endSchemeMap D.abelian.scheme (D.action (c b)) ≫ D.polarizationMap.hom

/-- The concrete PEL conditions on a candidate family. The Lie-type locus
is a further selection of these genuine objects in the eventual moduli input. -/
def IsPEL (D : PELFamilyData R g N S) (δ : Fin g → ℕ) (c : R →+* R) : Prop :=
  D.polarizationMap.HasPolarizationType δ ∧
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D.dual D.polarizationMap.hom K s) ∧
    D.IsRosatiCompatible c

/-- Forget only the positivity proofs from HilbertConstruction's actual polarized family. -/
abbrev ofPolarized {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (action : R →+* End.IntegralEnd A.abelian.scheme) : PELFamilyData R g N S where
  abelian := A.abelian
  dual := A.dual
  polarizationMap := A.polarization.isogeny
  marking := A.level
  action := action

/-- The underlying HilbertConstruction polarized object is reconstructed from its stated
geometric positivity and kernel-type conditions. -/
abbrev toPolarized (D : PELFamilyData R g N S) {δ : Fin g → ℕ} {c : R →+* R}
    (h : D.IsPEL δ c) : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := D.abelian
  dual := D.dual
  polarization := ⟨D.polarizationMap, h.1, h.2.1⟩
  level := D.marking

theorem ofPolarized_isPEL {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (action : R →+* End.IntegralEnd A.abelian.scheme) (c : R →+* R)
    (hRosati : (ofPolarized A action).IsRosatiCompatible c) :
    (ofPolarized A action).IsPEL δ c :=
  ⟨A.polarization.kernelType, A.polarization.positive, hRosati⟩

/-- Base change of every piece of the candidate family. The integral
endomorphism action uses the proved ring homomorphism from BaseChange. -/
abbrev pullback (D : PELFamilyData R g N S) (f : T ⟶ S) : PELFamilyData R g N T where
  abelian := D.abelian.pullback f
  dual := D.dual.pullback f
  polarizationMap := D.polarizationMap.pullback f
  marking := D.marking.pullback f
  action := (BaseChange.endBaseChange D.abelian.scheme f).comp D.action

@[simp]
theorem pullback_action_schemeMap (D : PELFamilyData R g N S) (f : T ⟶ S) (b : R) :
    End.endSchemeMap (D.pullback f).abelian.scheme ((D.pullback f).action b) =
      (Over.pullback f).map (End.endSchemeMap D.abelian.scheme (D.action b)) :=
  BaseChange.endBaseChange_schemeMap D.abelian.scheme f (D.action b)

end PELFamilyData

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PEL
