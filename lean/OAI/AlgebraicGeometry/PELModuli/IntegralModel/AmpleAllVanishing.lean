import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmplePowerVanishing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPower
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism

/-! # Ample All Vanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleAllVanishing

noncomputable section

section

/-! Serre vanishing holds for every sufficiently large actual tensor
power, using finitely many residue classes of the embedding degree. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory

local instance (X : Scheme.{0}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem ample_tensorPowers_eventually_vanishing
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H (M ⊗ (L.tensorPower n).sheaf) q) := by
  classical
  obtain ⟨d, hd, hstep⟩ := AmplePowerVanishing.ample_tensorPowers_vanishing_step f L hL
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

end

section

/-! All positive cohomology groups of sufficiently high ample powers
vanish on a proper scheme over a noetherian affine base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

local instance (X : Scheme.{0}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem ample_lineBundle_eventually_vanishing
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H (L.tensorPower n).sheaf q) := by
  let O := AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X
  have : O.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  have : O.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  have : O.IsFiniteType := by
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData O
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  obtain ⟨b, hb⟩ := ample_tensorPowers_eventually_vanishing f L hL O
  refine ⟨b, fun n hn q hq => ?_⟩
  have : Subsingleton (SheafCohomology.AffineH.Projective.H (O ⊗ (L.tensorPower n).sheaf) q) := hb n hn q hq
  let e : O ⊗ (L.tensorPower n).sheaf ≅ (L.tensorPower n).sheaf :=
    ((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl _) ≪≫ λ_ _
  exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor X q).map e.inv)).injective.subsingleton

end

/-! One constructed positive power of an ample line bundle has both
a finite generating section family and vanishing positive cohomology. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ample_exists_power_sections_and_vanishing
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ (d : ℕ) (_ : 0 < d) (n : ℕ)
      (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf)),
      (∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) ∧
      ∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H (L.tensorPower d).sheaf q) := by
  obtain ⟨d, hd, n, s, hs, _⟩ := hL.projective_section_family
  obtain ⟨b, hb⟩ := ample_lineBundle_eventually_vanishing f (L.tensorPower d)
    (hL.tensorPower d hd)
  let e : ((L.tensorPower d).tensorPower (b + 1)).sheaf ≅
      (L.tensorPower ((b + 1) * d)).sheaf := (L.tensorPowerComposeIso (b + 1) d).symm
  let t := fun i : Fin (n + 1) => AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection (s i) (b + 1) ≫ e.hom
  refine ⟨(b + 1) * d, Nat.mul_pos (Nat.zero_lt_succ b) hd, n, t, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hs x
    refine ⟨i, ?_⟩
    have he : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i) = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
      (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso _ e).trans
        (AbelianModuli.HilbertConstruction.Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := L.tensorPower d) (s i)
          (b + 1) (Nat.zero_lt_succ b))
    exact he.symm ▸ hi
  · intro q hq
    have : Subsingleton (SheafCohomology.AffineH.Projective.H ((L.tensorPower d).tensorPower (b + 1)).sheaf q) :=
      hb (b + 1) (Nat.le_succ b) q hq
    exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor X q).map e.inv)).injective.subsingleton

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleAllVanishing
