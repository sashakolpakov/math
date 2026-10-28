import OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionLifting
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ProductSurjectivity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Short Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ShortExact.CrystallineCechShortExact

noncomputable section

/-!
# Short exact sequences of native principal Čech complexes

Surjectivity on native sections gives surjectivity on every product of
intersection sections. Together with kernel preservation this makes the
actual Čech sequence short exact in every degree. Vanishing of first
Čech cohomology on every native object supplies the required section lifts.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

theorem degree_epi {F G : Sheaf J V} (φ : F ⟶ G)
    (hφ : ∀ T : Site.Object p k X, Epi (φ.hom.app (op T))) (n : ℕ) :
    Epi (((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).map φ).f n) := by
  change Epi (Limits.Pi.map (fun t : ((N).obj (op ⦋n⦌)).I => φ.hom.app
    (op (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋n⦌)).obj t)))))
  apply Module.ProductSurjectivity.ModuleProductSurjectivity.epi.{u + 1, u, u + 1}
  intro t
  exact hφ _

theorem shortExact (S : ShortComplex (Sheaf J V)) (hS : S.ShortExact)
    (hφ : ∀ T : Site.Object p k X, Epi (S.g.hom.app (op T))) :
    (CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.shortComplex p k X Q s S).ShortExact := by
  have := hS.mono_f
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.degree_exact p k X Q s S hS.exact n
  · exact CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.degree_mono p k X Q s S n
  · exact degree_epi p k X Q s S.g hφ n

theorem shortExact_of_cech_one (S : ShortComplex (Sheaf J V)) (hS : S.ShortExact)
    (hA : ∀ (T : Site.Object p k X) (t : Finset T.thickening.ring),
      Ideal.span (t : Set T.thickening.ring) = ⊤ →
        ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X T (fun s : t => s.val)).obj S.X₁).ExactAt 1) :
    (CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.shortComplex p k X Q s S).ShortExact :=
  shortExact p k X Q s S hS (fun T => SectionLifting.CrystallineSectionLifting.epi p k X T S hS (hA T))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ShortExact.CrystallineCechShortExact
