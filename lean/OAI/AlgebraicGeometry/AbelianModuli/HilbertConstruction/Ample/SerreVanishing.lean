import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerSerreVanishingStep
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteModuleTensorAssociativity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition

/-! # Serre Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SerreVanishing

noncomputable section

/-! One uniform bound kills every positive genuine cohomology group of every sufficiently high ample twist, by the finite residue classes of a constructed embedding degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem ample_tensorPowers_eventually_vanish
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (L : Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n → ∀ q : ℕ,
      IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).obj
        (Tensor.ProductSheaf.tensorModule M (L.tensorPower n).sheaf)) := by
  classical
  obtain ⟨d, hd, hstep⟩ := PowerSerreVanishingStep.ample_tensorPowers_vanishing_step f L hL
  let F (k : Fin d) : X.Modules := Tensor.ProductSheaf.tensorModule M (L.tensorPower k.val).sheaf
  have hv (k : Fin d) : ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ,
      IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).obj
        (Tensor.ProductSheaf.tensorModule (F k) (L.tensorPower (n * d)).sheaf)) := by
    have : (F k).IsQuasicoherent := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M (L.tensorPower k.val)
    have : (F k).IsFiniteType := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_finiteType M (L.tensorPower k.val)
    exact hstep (F k)
  choose b hb using hv
  let B := Finset.univ.sup b
  refine ⟨B * d, fun n hn q ↦ ?_⟩
  let k : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hk : b k ≤ n / d :=
    (Finset.le_sup (f := b) (Finset.mem_univ k)).trans ((Nat.le_div_iff_mul_le hd).mpr hn)
  have he : k.val + n / d * d = n := by
    change n % d + n / d * d = n
    rw [Nat.mul_comm (n / d) d]
    exact Nat.mod_add_div n d
  let eP := (L.tensorPowerAddIso k.val (n / d * d)).symm ≪≫
    eqToIso (congrArg (fun m => (L.tensorPower m).sheaf) he)
  let e := ConcreteModuleTensorAssociativity.actualModuleTensorAssoc M (L.tensorPower k.val).sheaf
      (L.tensorPower (n / d * d)).sheaf ≪≫ Tensor.ProductSheaf.tensorModuleCongr (Iso.refl M) eP
  exact (hb k (n / d) hk q).of_iso
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).mapIso e).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SerreVanishing
