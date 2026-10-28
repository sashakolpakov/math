import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Block
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitOrdinary

/-! # Ordinary Frobenius -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFrobenius.Construction

noncomputable section

/-!
The full X-kernel uses each actual chosen multiplicative factor and its
opposite annihilator. Its equality with the native Frobenius kernel is
proved from the ordinary block splittings and source Cartier pairings.
No Frobenius-kernel or quotient compatibility is stored in the data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The native source geometry of one conjugate pair of ordinary blocks.
The pairing is the source polarized Cartier identification; its
annihilator and all kernel properties are constructed below. -/
structure NativeOrdinaryPairedBlock (p : ℕ) (k : Type u) [Field k] where
  chosen : Grp (Over (Spec (.of k)))
  opposite : Grp (Over (Spec (.of k)))
  multiplicativeHeight : ℕ
  etaleHeight : ℕ
  splitting : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k chosen p 1 multiplicativeHeight etaleHeight
  coordinates : CartierModel.Construction.CartierCoordinates (.of k) chosen
  pairing : opposite ≅ coordinates.dualGroup

namespace NativeOrdinaryPairedBlock

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] (D : NativeOrdinaryPairedBlock p k)

abbrev chosenKernel : Grp (Over (Spec (.of k))) :=
  OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k p 1 D.multiplicativeHeight

abbrev chosenKernelCoordinates : CartierModel.Construction.CartierCoordinates (.of k) D.chosenKernel :=
  MultiplicativeDual.Construction.diagonalizableCartierCoordinates k (OrdinaryBlocks.Construction.OrdinaryBlockLabels p 1 D.multiplicativeHeight)

def etaleCoordinates : CartierModel.Construction.CartierCoordinates (.of k) (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 D.etaleHeight) := by
  have : IsCommMonObj (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 D.etaleHeight).X :=
    inferInstanceAs (IsCommMonObj (EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k))
      (OrdinaryBlocks.Construction.OrdinaryBlockLabels p 1 D.etaleHeight)).X)
  have h := OrdinaryBlocks.Construction.etaleOrdinaryBlock_finiteLocallyFree k p 1 D.etaleHeight
  have : IsFinite (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 D.etaleHeight).X.hom := h.1
  have : Flat (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 D.etaleHeight).X.hom := h.2.1
  have : LocallyOfFinitePresentation (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 D.etaleHeight).X.hom := h.2.2
  exact CartierModel.Construction.cartierCoordinates (.of k) _

abbrev chosenInclusion : D.chosenKernel ⟶ D.chosen :=
  OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k D.splitting

def kernel : Grp (Over (Spec (.of k))) :=
  D.coordinates.pairedKernel D.chosenKernelCoordinates D.chosenInclusion

def inclusion : D.kernel ⟶ D.chosen ⊗ D.opposite :=
  D.coordinates.pairedKernelInclusion D.chosenKernelCoordinates D.chosenInclusion D.pairing

theorem inclusion_closed : IsClosedImmersion D.inclusion.hom.hom.left :=
  D.coordinates.pairedKernelInclusion_closed D.chosenKernelCoordinates D.chosenInclusion D.pairing
    (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion_closed k D.splitting)

theorem kernel_finiteLocallyFree :
    IsFinite D.kernel.X.hom ∧ Flat D.kernel.X.hom ∧ LocallyOfFinitePresentation D.kernel.X.hom := by
  have h := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock_finiteLocallyFree k p 1 D.multiplicativeHeight
  have : IsFinite D.chosenKernel.X.hom := h.1
  have : Flat D.chosenKernel.X.hom := h.2.1
  have : LocallyOfFinitePresentation D.chosenKernel.X.hom := h.2.2
  exact D.coordinates.pairedKernel_finiteLocallyFree D.chosenKernelCoordinates D.chosenInclusion

variable [CharP k p] [PerfectRing k p]

theorem kernel_trivialFrobenius :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) D.kernel.X = 1 :=
  OrdinaryOpposite.Construction.ordinaryPairedKernel_trivialFrobenius p k D.splitting D.coordinates
    D.chosenKernelCoordinates D.etaleCoordinates

omit [PerfectRing k p] in
theorem factor_of_trivialFrobenius (T : Grp (Over (Spec (.of k))))
    (f : T ⟶ D.chosen ⊗ D.opposite)
    (hT : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) T.X = 1) :
    ∃ a : T.X ⟶ D.kernel.X, a ≫ D.inclusion.hom.hom = f.hom.hom := by
  have : Etale (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 D.etaleHeight).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  have : Etale D.chosenKernelCoordinates.dualGroup.X.hom :=
    MultiplicativeDual.Construction.diagonalizableCartierDual_etale k (OrdinaryBlocks.Construction.OrdinaryBlockLabels p 1 D.multiplicativeHeight)
  exact OrdinaryFactorization.Construction.pairedFactor_of_trivialFrobenius p (Fact.out : p.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) D.splitting
    D.coordinates D.chosenKernelCoordinates D.pairing f hT

end NativeOrdinaryPairedBlock

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (n : ℕ) (D : Fin n → NativeOrdinaryPairedBlock p k)
variable (split : Assembly.Construction.torsionGroup A p ≅ BlockProducts.Construction.groupBlockProduct n (fun v => (D v).chosen ⊗ (D v).opposite))

/-- The actual full chosen/opposite prescription, embedded through A[p]. -/
def fullOrdinaryPairedKernelToAbelian : (BlockProducts.Construction.groupBlockProduct n (fun v => (D v).kernel)).X ⟶ A.scheme :=
  Assembly.Construction.fullKernelToAbelian A p n (fun v => (D v).kernel) (fun v => (D v).chosen ⊗ (D v).opposite)
    (fun v => (D v).inclusion) split

omit [IsAlgClosed k] [CharP k p] in
theorem fullOrdinaryPairedKernelToAbelian_eq_paired :
    fullOrdinaryPairedKernelToAbelian p k A n D split =
      PairedKernels.Construction.fullPairedKernelToAbelian A p n (fun v => (D v).chosen) (fun v => (D v).chosenKernel)
        (fun v => (D v).opposite) (fun v => (D v).coordinates)
        (fun v => (D v).chosenKernelCoordinates) (fun v => (D v).chosenInclusion)
        (fun v => (D v).pairing) split := rfl

instance fullOrdinaryPairedKernelToAbelian_isMonHom :
    IsMonHom (fullOrdinaryPairedKernelToAbelian p k A n D split) := by
  unfold fullOrdinaryPairedKernelToAbelian
  infer_instance

instance fullOrdinaryPairedKernelToAbelian_closed :
    IsClosedImmersion (fullOrdinaryPairedKernelToAbelian p k A n D split).left :=
  Assembly.Construction.fullKernelToAbelian_closed A p n _ _ _ (fun v => (D v).inclusion_closed) split

instance fullOrdinaryPairedKernelToAbelian_mono :
    Mono (fullOrdinaryPairedKernelToAbelian p k A n D split) :=
  Over.mono_of_mono_left _

/-- Exact all-test kernel equality for the full native ordinary prescription. -/
theorem fullOrdinaryPaired_frobeniusKernel :
    Prescribed.Construction.PrescribedKernel (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom
      (fullOrdinaryPairedKernelToAbelian p k A n D split) :=
  Block.Construction.fullBlockKernel_is_frobeniusKernel p k A n _ _ _ split
    (fun v => (D v).kernel_trivialFrobenius) (fun v => (D v).inclusion_closed)
    (fun v => (D v).factor_of_trivialFrobenius)

theorem fullOrdinaryPaired_frobeniusKernel_subobject :
    Subobject.mk (fullOrdinaryPairedKernelToAbelian p k A n D split) =
      Subobject.mk (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom) :=
  Subobject.mk_eq_mk_of_comm _ _
    (Prescribed.Construction.prescribedKernelIso (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
      (fullOrdinaryPaired_frobeniusKernel p k A n D split))
    (Prescribed.Construction.prescribedKernelIso_inclusion (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
      (fullOrdinaryPaired_frobeniusKernel p k A n D split))

def fullOrdinaryPairedFrobeniusQuotientIso :
    BaseChange.Construction.subgroupQuotient (fullOrdinaryPairedKernelToAbelian p k A n D split) ≅
      (BaseChange.Construction.fppfPoints (Spec (.of k))).obj
        (A.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p (Fact.out : p.Prime) _
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)))).scheme :=
  Prescribed.Construction.prescribedFrobeniusQuotientIsoOfHomomorphisms (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
    (fullOrdinaryPaired_frobeniusKernel p k A n D split)
    (SplitOrdinary.Construction.geometricFrobenius_isFppfQuotient p k A)

theorem fullOrdinaryPairedFrobeniusQuotientIso_projection :
    Prescribed.Construction.subgroupQuotientProjection (fullOrdinaryPairedKernelToAbelian p k A n D split) ≫
        (fullOrdinaryPairedFrobeniusQuotientIso p k A n D split).hom =
      (BaseChange.Construction.fppfPoints (Spec (.of k))).map (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom :=
  Prescribed.Construction.prescribedFrobeniusQuotientIsoOfHomomorphisms_projection (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
    (fullOrdinaryPaired_frobeniusKernel p k A n D split)
    (SplitOrdinary.Construction.geometricFrobenius_isFppfQuotient p k A)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFrobenius.Construction
