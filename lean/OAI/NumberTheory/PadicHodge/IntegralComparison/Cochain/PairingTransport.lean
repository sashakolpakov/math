import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality

/-! # Pairing Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.PairingTransport

noncomputable section

/-! Bilinear cochain products and their actual graded differential rule
transport through a chain isomorphism, naturally in commuting squares. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality.Cohomology
universe u v
variable {R : Type u} [CommRing R]
  {K L : CochainComplex (ModuleCat.{v} R) ℕ} (e : K ≅ L)
  (μ : ∀ n m, L.X n →ₗ[R] L.X m →ₗ[R] L.X (n + m))

def cup (n m : ℕ) : K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m) :=
  (((μ n m).comp (e.hom.f n).hom).compl₂ (e.hom.f m).hom).compr₂ (e.inv.f (n + m)).hom

theorem hom_cup (n m : ℕ) (x : K.X n) (y : K.X m) :
    e.hom.f (n + m) (cup e μ n m x y) = μ n m (e.hom.f n x) (e.hom.f m y) := by
  exact ConcreteCategory.congr_hom (congrArg (fun f : L ⟶ L => f.f (n + m)) e.inv_hom_id)
    (μ n m (e.hom.f n x) (e.hom.f m y))

theorem map_cast {A B : CochainComplex (ModuleCat.{v} R) ℕ} (f : A ⟶ B)
    {n m : ℕ} (h : n = m) (x : A.X n) :
    f.f m (CohomologyCup.degreeCast A h x) = CohomologyCup.degreeCast B h (f.f n x) := by
  subst m
  rfl

theorem hom_cupInto (n m k : ℕ) (h : n + m = k) (x : K.X n) (y : K.X m) :
    e.hom.f k (CohomologyCup.cupInto K (cup e μ) n m k h x y) =
      CohomologyCup.cupInto L μ n m k h (e.hom.f n x) (e.hom.f m y) := by
  change e.hom.f k (CohomologyCup.degreeCast K h (cup e μ n m x y)) = _
  rw [map_cast, hom_cup]
  rfl

theorem comm_apply {A B : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : A ⟶ B) (n m : ℕ) (x : A.X n) :
    f.f m (A.d n m x) = B.d n m (f.f n x) :=
  ConcreteCategory.congr_hom (f.comm n m).symm x

variable (hμ : ∀ n m (x : L.X n) (y : L.X m),
  L.d (n + m) (n + m + 1) (μ n m x y) =
    CohomologyCup.cupInto L μ (n + 1) m (n + m + 1) (by omega) (L.d n (n + 1) x) y +
      (-1 : ℤ) ^ n • CohomologyCup.cupInto L μ n (m + 1) (n + m + 1) (by omega) x (L.d m (m + 1) y))

include hμ in
theorem differential (n m : ℕ) (x : K.X n) (y : K.X m) :
    K.d (n + m) (n + m + 1) (cup e μ n m x y) =
      CohomologyCup.cupInto K (cup e μ) (n + 1) m (n + m + 1) (by omega) (K.d n (n + 1) x) y +
        (-1 : ℤ) ^ n • CohomologyCup.cupInto K (cup e μ) n (m + 1) (n + m + 1) (by omega) x (K.d m (m + 1) y) := by
  apply ((HomologicalComplex.eval _ _ (n + m + 1)).mapIso e).toLinearEquiv.injective
  change e.hom.f (n + m + 1) _ = e.hom.f (n + m + 1) _
  rw [comm_apply, hom_cup, hμ, map_add, map_zsmul, hom_cupInto, hom_cupInto,
    comm_apply, comm_apply]

variable {K' L' : CochainComplex (ModuleCat.{v} R) ℕ} (e' : K' ≅ L')
  (ν : ∀ n m, L'.X n →ₗ[R] L'.X m →ₗ[R] L'.X (n + m))
  (f : K ⟶ K') (g : L ⟶ L') (h : f ≫ e'.hom = e.hom ≫ g)
  (hg : ∀ n m (x : L.X n) (y : L.X m),
    g.f (n + m) (μ n m x y) = ν n m (g.f n x) (g.f m y))

include h hg in
theorem naturality (n m : ℕ) (x : K.X n) (y : K.X m) :
    f.f (n + m) (cup e μ n m x y) = cup e' ν n m (f.f n x) (f.f m y) := by
  have hs (a : ℕ) (z : K.X a) : e'.hom.f a (f.f a z) = g.f a (e.hom.f a z) :=
    ConcreteCategory.congr_hom (congrArg (fun b : K ⟶ L' => b.f a) h) z
  apply ((HomologicalComplex.eval _ _ (n + m)).mapIso e').toLinearEquiv.injective
  change e'.hom.f (n + m) _ = e'.hom.f (n + m) _
  rw [hs, hom_cup, hg, hom_cup, hs, hs]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.PairingTransport
