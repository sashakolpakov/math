import OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGalois
import OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry

/-! # Geometric Naturality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricNaturality

noncomputable section

/-!
# Galois naturality for all morphisms of geometric fibers

The geometric Galois isomorphisms commute with the base change of every
morphism over the base field. In particular this includes every endomorphism
of an integral model after passing to its geometric generic fiber.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGalois

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

def geometricFiberFunctor : Over (Spec (CommRingCat.of K)) ⥤ Scheme.{u} :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙ Over.forget _

theorem geometricFiberFunctor_map_fst {M N : Over (Spec (CommRingCat.of K))} (g : M ⟶ N) :
    (geometricFiberFunctor K L).map g ≫ pullback.fst N.hom _ =
      pullback.fst M.hom _ ≫ g.left :=
  pullback.lift_fst _ _ _

theorem geometricFiberFunctor_map_snd {M N : Over (Spec (CommRingCat.of K))} (g : M ⟶ N) :
    (geometricFiberFunctor K L).map g ≫ pullback.snd N.hom _ =
      pullback.snd M.hom _ :=
  pullback.lift_snd _ _ _

theorem geometricFiberIso_natural (σ : L ≃ₐ[K] L)
    {M N : Over (Spec (CommRingCat.of K))} (g : M ⟶ N) :
    (geometricFiberFunctor K L).map g ≫ (IntegralComparison.Frobenius.Geometry.geometricFiberIso N.hom σ).hom =
      (IntegralComparison.Frobenius.Geometry.geometricFiberIso M.hom σ).hom ≫ (geometricFiberFunctor K L).map g := by
  let a : IntegralComparison.Frobenius.Geometry.geometricFiber (L := L) M.hom ⟶ IntegralComparison.Frobenius.Geometry.geometricFiber (L := L) N.hom :=
    (geometricFiberFunctor K L).map g
  have hf : a ≫ pullback.fst N.hom _ = pullback.fst M.hom _ ≫ g.left :=
    geometricFiberFunctor_map_fst K L g
  have hs : a ≫ pullback.snd N.hom _ = pullback.snd M.hom _ :=
    geometricFiberFunctor_map_snd K L g
  change a ≫ (IntegralComparison.Frobenius.Geometry.geometricFiberIso N.hom σ).hom = (IntegralComparison.Frobenius.Geometry.geometricFiberIso M.hom σ).hom ≫ a
  apply pullback.hom_ext
  · rw [Category.assoc, IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_fst, hf,
      Category.assoc, hf,
      ← Category.assoc (IntegralComparison.Frobenius.Geometry.geometricFiberIso M.hom σ).hom, IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_fst]
  · rw [Category.assoc, IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_snd,
      ← Category.assoc a, hs, Category.assoc, hs, IntegralComparison.Frobenius.Geometry.geometricFiberIso_hom_snd]

/-- The geometric Galois isomorphism is natural for every morphism over K. -/
def geometricGaloisNatIso (σ : L ≃ₐ[K] L) :
    geometricFiberFunctor K L ≅ geometricFiberFunctor K L :=
  NatIso.ofComponents (fun M => IntegralComparison.Frobenius.Geometry.geometricFiberIso M.hom σ)
    (fun g => geometricFiberIso_natural K L σ g)

theorem geometricGaloisNatIso_one :
    geometricGaloisNatIso K L (1 : L ≃ₐ[K] L) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact congrArg Iso.hom (GeometricGalois.geometricFiberIso_one M.hom)

theorem geometricGaloisNatIso_mul (σ τ : L ≃ₐ[K] L) :
    geometricGaloisNatIso K L (σ * τ) =
      geometricGaloisNatIso K L σ ≪≫ geometricGaloisNatIso K L τ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact congrArg Iso.hom (GeometricGalois.geometricFiberIso_mul M.hom σ τ)

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry

variable (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem integralEndomorphism_galois (M : IntegralGeometry.IntegralModel p K) (g : End M)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ((IntegralGeometry.genericFiberFunctor p K ⋙ geometricFiberFunctor K (AlgebraicClosure K)).map g) ≫
        (IntegralComparison.Frobenius.Geometry.geometricFiberIso ((IntegralGeometry.genericFiberFunctor p K).obj M).hom σ).hom =
      (IntegralComparison.Frobenius.Geometry.geometricFiberIso ((IntegralGeometry.genericFiberFunctor p K).obj M).hom σ).hom ≫
        ((IntegralGeometry.genericFiberFunctor p K ⋙ geometricFiberFunctor K (AlgebraicClosure K)).map g) :=
  geometricFiberIso_natural K (AlgebraicClosure K) σ ((IntegralGeometry.genericFiberFunctor p K).map g)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricNaturality
