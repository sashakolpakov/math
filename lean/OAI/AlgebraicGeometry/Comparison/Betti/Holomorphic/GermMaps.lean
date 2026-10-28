import OAI.AlgebraicGeometry.Comparison.Betti.GermComposition
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms

/-! # Germ Maps -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps.AnalyticLocal

noncomputable section

section

/-! Constants and actual holomorphic pullback on the existing local rings
of holomorphic germs. These preserve point evaluation and composition. -/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

def holomorphicConstantHom (x : E) : ℂ →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x where
  toFun c := ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x (fun _ => c) isOpen_univ (mem_univ x) (differentiableOn_const c)
  map_zero' := by apply Subtype.ext; rfl
  map_one' := by apply Subtype.ext; rfl
  map_add' a b := by apply Subtype.ext; rfl
  map_mul' a b := by apply Subtype.ext; rfl

instance holomorphicGermAlgebra (x : E) : Algebra ℂ (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) :=
  (holomorphicConstantHom x).toAlgebra

def holomorphicComposition (f : F → E) (hf : Differentiable ℂ f) (y : F) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f y) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y where
  toFun a := ⟨GermComposition.AnalyticLocal.germComposition f hf.continuous.continuousAt a.val, by
    obtain ⟨u, hua, U, hU, hyU, hu⟩ := a.property
    refine ⟨u ∘ f, ?_, f ⁻¹' U, hU.preimage hf.continuous, hyU, ?_⟩
    · rw [← hua]
      rfl
    · exact hu.comp hf.differentiableOn (fun _ hp => hp)⟩
  map_zero' := by apply Subtype.ext; exact map_zero (GermComposition.AnalyticLocal.germComposition f hf.continuous.continuousAt)
  map_one' := by apply Subtype.ext; exact map_one (GermComposition.AnalyticLocal.germComposition f hf.continuous.continuousAt)
  map_add' a b := by apply Subtype.ext; exact map_add (GermComposition.AnalyticLocal.germComposition f hf.continuous.continuousAt) a.val b.val
  map_mul' a b := by apply Subtype.ext; exact map_mul (GermComposition.AnalyticLocal.germComposition f hf.continuous.continuousAt) a.val b.val

def holomorphicCompositionAlgHom (f : F → E) (hf : Differentiable ℂ f) (y : F) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f y) →ₐ[ℂ] ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y where
  __ := holomorphicComposition f hf y
  commutes' c := by apply Subtype.ext; rfl

theorem holomorphicComposition_value (f : F → E) (hf : Differentiable ℂ f) (y : F)
    (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f y)) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom y (holomorphicComposition f hf y a) = ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom (f y) a :=
  GermComposition.AnalyticLocal.germComposition_value f y hf.continuous.continuousAt a.val

theorem holomorphicComposition_id (x : E) :
    holomorphicComposition id differentiable_id x = RingHom.id _ := by
  ext a
  exact DFunLike.congr_fun GermComposition.AnalyticLocal.germComposition_id a.val

theorem holomorphicComposition_comp (f : F → E) (hf : Differentiable ℂ f)
    (g : G → F) (hg : Differentiable ℂ g) (z : G) :
    (holomorphicComposition g hg z).comp (holomorphicComposition f hf (g z)) =
      holomorphicComposition (f ∘ g) (hf.comp hg) z := by
  ext a
  exact DFunLike.congr_fun (GermComposition.AnalyticLocal.germComposition_comp f hf.continuous.continuousAt
    g hg.continuous.continuousAt) a.val

end

/-! Identifying equal base points transports holomorphic germs while
preserving their actual function representatives. -/

open Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x y : E}

def holomorphicGermPointEquiv (h : x = y) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y :=
  h ▸ RingEquiv.refl (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)

theorem holomorphicGermPointEquiv_val (h : x = y) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) (f : E → ℂ)
    (ha : a.val = (f : Germ (𝓝 x) ℂ)) :
    (holomorphicGermPointEquiv h a).val = (f : Germ (𝓝 y) ℂ) := by
  subst y
  exact ha

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps.AnalyticLocal
