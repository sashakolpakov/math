import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient

/-! # Ideal Quotient Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientTransition

noncomputable section

/-! Canonical transitions between coefficient-ideal quotients of the original module complexes. -/

open _root_.CategoryTheory

universe u v

variable (R : Type u) [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)

def component (M : ModuleCat.{v} R) : (IdealQuotient.functor R I).obj M ⟶
    (IdealQuotient.functor R J).obj M :=
  ModuleCat.ofHom (Submodule.mapQ (I • ⊤) (J • ⊤) (LinearMap.id : M →ₗ[R] M) (by
    simpa only [Submodule.comap_id] using (Submodule.smul_mono hIJ (le_refl (⊤ : Submodule R M)))))

theorem component_mk (M : ModuleCat.{v} R) (x : M) : component R I J hIJ M (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk x := rfl

def transformation : IdealQuotient.functor.{u, v} R I ⟶ IdealQuotient.functor R J where
  app := component R I J hIJ
  naturality M N f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R M).mkQ_surjective x
    rfl

theorem projection : IdealQuotient.projection.{u, v} R I ≫ transformation R I J hIJ =
    IdealQuotient.projection R J := by
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def complexMap (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    IdealQuotient.complex R I K ⟶ IdealQuotient.complex R J K :=
  ((transformation R I J hIJ).mapHomologicalComplex (ComplexShape.up ℕ)).app K

theorem complexProjection (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    IdealQuotient.complexProjection R I K ≫ complexMap R I J hIJ K =
      IdealQuotient.complexProjection R J K := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientTransition
