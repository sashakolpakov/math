import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Torsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Etale

/-! # Ordinary -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Ordinary.Construction

noncomputable section

/-!
Identify Frobenius kernels from native ordinary splittings. The finite
kernel is first placed in p-torsion by the proved height-one argument;
the etale component then vanishes because its Frobenius is invertible.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

section EtaleDetection

variable {S : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
variable {H E : Over S} [GrpObj H] [GrpObj E] [Etale E.hom]

theorem map_to_etale_of_trivial_frobenius (f : H ⟶ E) [IsMonHom f]
    (hH : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS H = 1) : f = 1 := by
  let FE := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS E
  have : Mono FE := Over.mono_of_mono_left FE
  let P := Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)
  let j : Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS H ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS E := P.map f
  have : IsMonHom j := Functor.map.instIsMonHom (F := P) (f := f) H E
  apply (cancel_mono FE).mp
  have hn := (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat p hp hS).naturality f
  exact hn.trans ((congrArg (fun a => a ≫ j) hH).trans
    ((MonObj.one_comp j).trans (MonObj.one_comp FE).symm))

end EtaleDetection

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (M E : Grp (Over (Spec (.of k))))
variable (e : Assembly.Construction.torsionGroup A p ≅ M ⊗ E)

/-- The independently prescribed multiplicative factor is included through
the actual p-torsion scheme of the abelian variety. -/
def ordinaryFactorToAbelian : M.X ⟶ A.scheme :=
  (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom ≫ e.inv.hom.hom ≫ A.torsionInclusion p

instance ordinaryFactorToAbelian_isMonHom : IsMonHom (ordinaryFactorToAbelian p k A M E e) := by
  let j : M.X ⟶ A.torsionScheme p := (AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ e.inv).hom.hom
  have : IsMonHom j := inferInstanceAs (IsMonHom (AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ e.inv).hom.hom)
  change IsMonHom (j ≫ A.torsionInclusion p)
  infer_instance

instance ordinaryFactorToAbelian_mono : Mono (ordinaryFactorToAbelian p k A M E e) := by
  have : Mono (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom := mono_of_mono_fac
    (show (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom ≫ fst M.X E.X = 𝟙 M.X from lift_fst _ _)
  unfold ordinaryFactorToAbelian
  infer_instance

def frobeniusKernelToOrdinaryFactor : (Torsion.Construction.nativeFrobeniusKernel p k A).X ⟶ M.X :=
  Torsion.Construction.nativeFrobeniusKernelToTorsion p k A ≫ e.hom.hom.hom ≫ fst M.X E.X

theorem frobeniusKernelToOrdinaryFactor_inclusion [Etale E.X.hom] :
    frobeniusKernelToOrdinaryFactor p k A M E e ≫ ordinaryFactorToAbelian p k A M E e =
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom := by
  let H := (Torsion.Construction.nativeFrobeniusKernel p k A).X
  let : GrpObj H := Picard.PoincareBundle.Kernel.Scheme.kernelGroup (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom
  let t := Torsion.Construction.nativeFrobeniusKernelToTorsion p k A
  let a : H ⟶ M.X ⊗ E.X := t ≫ e.hom.hom.hom
  let j := (AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom
  have hc : a ≫ snd M.X E.X = 1 := by
    have : IsMonHom (a ≫ snd M.X E.X) := inferInstance
    exact map_to_etale_of_trivial_frobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) _
      (Torsion.Construction.nativeFrobeniusKernel_frobenius p k A)
  have ha : (a ≫ fst M.X E.X) ≫ j = a := by
    apply CartesianMonoidalCategory.hom_ext
    · change ((a ≫ fst M.X E.X) ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X)) ≫ fst M.X E.X = _
      rw [Category.assoc, lift_fst, Category.comp_id]
    · change ((a ≫ fst M.X E.X) ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X)) ≫ snd M.X E.X = _
      rw [Category.assoc, lift_snd, MonObj.comp_one]
      exact hc.symm
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 (A.torsionScheme p) :=
    congrArg (fun f : Assembly.Construction.torsionGroup A p ⟶ Assembly.Construction.torsionGroup A p => f.hom.hom) e.hom_inv_id
  change (a ≫ fst M.X E.X) ≫ j ≫ e.inv.hom.hom ≫ A.torsionInclusion p = _
  rw [← Category.assoc (a ≫ fst M.X E.X), ha]
  change (t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ≫ A.torsionInclusion p = _
  rw [Category.assoc t, ← Category.assoc e.hom.hom.hom, he, Category.id_comp]
  exact Torsion.Construction.nativeFrobeniusKernelToTorsion_inclusion p k A

/-- The ordinary factor is exactly the relative Frobenius kernel on all
test schemes, provided its Frobenius is trivial and the complement is etale. -/
theorem ordinaryFactor_is_frobeniusKernel [Etale E.X.hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) M.X = 1) :
    Prescribed.Construction.PrescribedKernel (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom (ordinaryFactorToAbelian p k A M E e) := by
  let F := (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom
  let i := ordinaryFactorToAbelian p k A M E e
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  have hi : i ≫ F = 1 := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal F M.X i).mpr
    (Picard.Homomorphisms.Diagonalizable.Construction.factors_kernel_of_trivial_relativeFrobenius p (Fact.out : p.Prime) hS M.X A.scheme hM i)
  intro T x
  constructor
  · intro hx
    let y := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv F T).symm ⟨x, hx⟩
    have hy : y ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F = x := congrArg Subtype.val
      ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv F T).apply_symm_apply ⟨x, hx⟩)
    let z := y ≫ frobeniusKernelToOrdinaryFactor p k A M E e
    have hz : z ≫ i = x := (Category.assoc _ _ _).trans
      ((congrArg (fun a => y ≫ a) (frobeniusKernelToOrdinaryFactor_inclusion p k A M E e)).trans hy)
    refine ⟨z, hz, fun b hb => (cancel_mono i).mp (hb.trans hz.symm)⟩
  · rintro ⟨y, hy, _⟩
    exact (congrArg (fun a => a ≫ F) hy.symm).trans
      ((Category.assoc y i F).trans ((congrArg (fun a => y ≫ a) hi).trans (MonObj.comp_one y)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Ordinary.Construction
