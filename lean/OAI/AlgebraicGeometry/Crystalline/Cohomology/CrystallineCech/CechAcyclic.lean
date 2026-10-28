import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCechExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ShortExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech
import Mathlib.Algebra.Homology.HomologySequence

/-! # Cech Acyclic -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.CechAcyclic.CrystallineCechAcyclic

noncomputable section

/-!
# Native Čech-acyclic sheaves and injective dimension shifting

Positive Čech vanishing on finite principal covers is stable under
isomorphism. Injective sheaves and the actual native frame terms satisfy
it. The cokernel of a monomorphism from such a sheaf into an injective
sheaf also satisfies it, by section lifting and the homology sequence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def Acyclic (F : Sheaf J V) : Prop :=
  ∀ (Q : Site.Object p k X) (t : Finset Q.thickening.ring),
    Ideal.span (t : Set Q.thickening.ring) = ⊤ → ∀ n : ℕ, n ≠ 0 →
      ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q (fun s : t => s.val)).obj F).ExactAt n

theorem of_iso {F G : Sheaf J V} (hF : Acyclic p k X F) (e : F ≅ G) : Acyclic p k X G := by
  intro Q t ht n hn
  exact (hF Q t ht n hn).of_iso
    ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q (fun s : t => s.val)).mapIso e)

theorem injective (I : Sheaf J V) [Injective I] : Acyclic p k X I := by
  intro Q t _ n hn
  exact InjectiveCechExact.CrystallineInjectiveCechExact.exactAt p k X Q (fun s : t => s.val) I n hn

theorem cokernel (S : ShortComplex (Sheaf J V)) (hS : S.ShortExact) [Injective S.X₂]
    (hA : Acyclic p k X S.X₁) : Acyclic p k X S.X₃ := by
  intro Q t ht n hn
  have hC := CrystallineCech.ShortExact.CrystallineCechShortExact.shortExact_of_cech_one p k X Q (fun s : t => s.val) S hS
    (fun T t ht => hA T t ht 1 (by decide))
  have hI := InjectiveCechExact.CrystallineInjectiveCechExact.exactAt p k X Q (fun s : t => s.val) S.X₂ n hn
  have hK := hA Q t ht (n + 1) (Nat.succ_ne_zero n)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hC.homology_exact₃ n (n + 1) (by simp)).isZero_X₂
    (hI.isZero_homology.eq_of_src _ _) (hK.isZero_homology.eq_of_tgt _ _)

variable (B σ : Type u) [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

theorem frame (n : ℕ) : Acyclic p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
    ((CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n) := by
  intro Q t ht j hj
  apply CrystallineFrame.SheafCech.CrystallineFrameSheafCech.exactAt p k B σ a Q n (fun s : t => s.val) _ j hj
  simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.CechAcyclic.CrystallineCechAcyclic
