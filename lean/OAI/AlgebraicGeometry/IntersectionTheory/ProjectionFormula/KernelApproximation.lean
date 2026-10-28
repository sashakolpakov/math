import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FreeSubmodule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SecondKernelDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

/-! # Kernel Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.KernelApproximation

noncomputable section

/-! Replacing a presentation kernel by a full-rank free submodule
gives a three-term free complex whose residual homology has smaller
projective dimension. Flat base change retains the actual residual module. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (B C : ModuleCat.{u} R)
  (g : B →ₗ[R] C) (N : Submodule R g.ker)

def map : N →ₗ[R] B := g.ker.subtype.comp N.subtype

theorem map_injective : Function.Injective (map R B C g N) :=
  g.ker.subtype_injective.comp N.subtype_injective

theorem comp_zero : g.comp (map R B C g N) = 0 := by
  ext x
  exact x.val.property

def complex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (map R B C g N) g (comp_zero R B C g N)

theorem toCycles_eq : (complex R B C g N).moduleCatToCycles = N.subtype := by
  ext x
  rfl

def homologyIso : (complex R B C g N).homology ≅ ModuleCat.of R (g.ker ⧸ N) :=
  (complex R B C g N).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (by rw [toCycles_eq, Submodule.range_subtype])).toModuleIso

theorem baseChange_length (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S] :
    Module.length S (ComplexDeterminantBaseChange.complex R S (map R B C g N) g
      (comp_zero R B C g N)).homology = Module.length S (S ⊗[R] (g.ker ⧸ N)) := by
  let F := ProjectionFormula.Flat.Extension.baseChange R S
  let e := (complex R B C g N).mapHomologyIso F ≪≫ F.mapIso (homologyIso R B C g N)
  exact e.toLinearEquiv.length_eq

theorem residual_dimension [Projective B] [Projective C] [Module.Free R N]
    (M : ModuleCat.{u} R) (π : C →ₗ[R] M) (he : Function.Exact g π)
    (hπ : Function.Surjective π) (d : ℕ) [HasProjectiveDimensionLE M (d + 3)] :
    HasProjectiveDimensionLE (ModuleCat.of R (g.ker ⧸ N)) (d + 1) := by
  let : HasProjectiveDimensionLE (ModuleCat.of R g.ker) (d + 1) :=
    SecondKernelDimension.bound R B C M g π he hπ (d + 1)
  let T := ShortComplex.moduleCatMk N.subtype N.mkQ (by ext; simp)
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
    (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
  exact hT.hasProjectiveDimensionLT_X₃ (d + 1)
    (inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R N) (d + 1)))
    (inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R g.ker) (d + 2)))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.KernelApproximation
