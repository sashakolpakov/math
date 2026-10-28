import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AmplePowerVanishing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPower
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent

/-! # Ample All Powers Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AmpleAllPowersVanishing

noncomputable section

/-! Serre vanishing holds for every sufficiently large actual tensor
power, using finitely many residue classes of the embedding degree. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory

namespace Cohomology

universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem ample_tensorPowers_eventually_vanishing
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H (M ⊗ (L.tensorPower n).sheaf) q) := by
  classical
  obtain ⟨d, hd, hstep⟩ := AmplePowerVanishing.Cohomology.ample_tensorPowers_vanishing_step f L hL
  let F (k : Fin d) : X.Modules := M ⊗ (L.tensorPower k.val).sheaf
  have hv (k : Fin d) : ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H (F k ⊗ (L.tensorPower (n * d)).sheaf) q) := by
    have hK := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (L.tensorPower k.val)
    have : (F k).IsQuasicoherent := hK.tensorObj_isQuasicoherent
    have : (F k).IsFiniteType := hK.tensorObj_isFiniteType
    exact hstep (F k)
  choose b hb using hv
  let B := Finset.univ.sup b
  refine ⟨B * d, fun n hn q hq => ?_⟩
  let k : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hk : b k ≤ n / d :=
    (Finset.le_sup (f := b) (Finset.mem_univ k)).trans ((Nat.le_div_iff_mul_le hd).mpr hn)
  have : Subsingleton (SheafCohomology.AffineH.Projective.H (F k ⊗ (L.tensorPower (n / d * d)).sheaf) q) :=
    hb k (n / d) hk q hq
  have he : k.val + n / d * d = n := by
    change n % d + n / d * d = n
    rw [Nat.mul_comm (n / d) d]
    exact Nat.mod_add_div n d
  let eP : (L.tensorPower k.val).sheaf ⊗ (L.tensorPower (n / d * d)).sheaf ≅
      (L.tensorPower n).sheaf :=
    SheafCohomology.Projective.TensorSections.monoidalTensorObjIso _ _ ≪≫ (Quotients.FiniteDescent.TensorPower.Construction.TensorPowerAddition.iso L.sheaf k.val (n / d * d)).symm ≪≫
      eqToIso (congrArg (fun m => (L.tensorPower m).sheaf) he)
  let e : F k ⊗ (L.tensorPower (n / d * d)).sheaf ≅ M ⊗ (L.tensorPower n).sheaf :=
    α_ M (L.tensorPower k.val).sheaf (L.tensorPower (n / d * d)).sheaf ≪≫
      (Iso.refl M ⊗ᵢ eP)
  exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor X q).map e.inv)).injective.subsingleton

end Cohomology

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AmpleAllPowersVanishing
