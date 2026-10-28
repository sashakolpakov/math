import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.FromDifferentials
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Stalk Differentials -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDifferentials

noncomputable section

/-! The absolute differential module of every stalk of a smooth
m-dimensional scheme over a field is finite free of rank m. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem data {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (m : ℕ) [SmoothOfRelativeDimension m f] (x : X) :
    letI := Stalk.PointAlgebra.scalarAlgebra f x
    Algebra.FormallySmooth K (X.presheaf.stalk x) ∧
      Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄K] ∧
      Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄K] ∧
      Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄K] = m := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := m) (f := f) x
  have hu : U = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _; exact (Subsingleton.elim (f x) y) ▸ e hx
  subst U
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f V
  let := Stalk.PointAlgebra.scalarAlgebra f x
  let : Algebra.IsStandardSmoothOfRelativeDimension m K Γ(X, V) :=
    Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra_standardSmooth m f V hstd
  let : Algebra.IsStandardSmooth K Γ(X, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth m
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  let : IsScalarTower K Γ(X, V) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun c => ((Stalk.ScalarMaps.germ f V x hx).commutes c).symm
  let M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization M (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  let : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk x) := Algebra.FormallyEtale.of_isLocalization M
  let : Algebra.FormallySmooth K (X.presheaf.stalk x) := Algebra.FormallySmooth.comp K Γ(X, V) _
  let eΩ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K Γ(X, V) (X.presheaf.stalk x)
  let : Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄K] := Module.Free.of_equiv eΩ
  let : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄K] := Module.Finite.equiv eΩ
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← eΩ.finrank_eq, Module.finrank_baseChange]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential m)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDifferentials
