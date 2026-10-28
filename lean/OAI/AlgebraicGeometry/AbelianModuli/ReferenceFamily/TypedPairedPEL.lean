import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELFunctor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelTypeInvariance

/-! # Typed Paired PEL -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The paired PEL moduli functor with the original prescribed finite
kernel type. Its natural involution preserves that type by the proved
geometric kernel comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T U V : Over (Spec (.of K))}
    (M : Type) [AddCommGroup M]

def Paired.PELFunctor.PairedPELClasses.HasKernelType : Paired.PELFunctor.PairedPELClasses P iota N n T → Prop :=
  Quotient.lift
    (fun A => (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel A.quotient.forward.isogeny.hom).HasModuleType M)
    (fun _ _ ⟨e⟩ => propext (e.kernel_moduleType_iff M))

theorem Paired.PELFunctor.PairedPELClasses.HasKernelType.pullback
    {q : Paired.PELFunctor.PairedPELClasses P iota N n T} (hq : q.HasKernelType M) (f : U ⟶ T) :
    (Paired.PELFunctor.PairedPELClasses.pullback f q).HasKernelType M := by
  induction q using Quotient.inductionOn with
  | h A => exact A.quotient.kernel_moduleType_pullback M hq f

theorem Paired.PELFunctor.PairedPELClasses.hasKernelType_swap_iff [CharZero K]
    (hn : 0 < n) (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (q : Paired.PELFunctor.PairedPELClasses P iota N n T) :
    (Paired.PELFunctor.PairedPELClasses.swap q).HasKernelType M ↔ q.HasKernelType M := by
  induction q using Quotient.inductionOn with
  | h A => exact (Paired.PELKernelModuleType.pairedPELQuotient_kernel_moduleType_iff A.quotient hn hdegree M).symm

def TypedPairedPEL.TypedPairedPELClasses (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N n : ℕ) (M : Type) [AddCommGroup M] (T : Over (Spec (.of K))) :=
  {q : Paired.PELFunctor.PairedPELClasses P iota N n T // q.HasKernelType M}

namespace TypedPairedPEL.TypedPairedPELClasses

def pullback (f : U ⟶ T) : TypedPairedPELClasses P iota N n M T →
    TypedPairedPELClasses P iota N n M U :=
  fun q => ⟨Paired.PELFunctor.PairedPELClasses.pullback f q.val,
    Paired.PELFunctor.PairedPELClasses.HasKernelType.pullback M q.property f⟩

theorem pullback_id (q : TypedPairedPELClasses P iota N n M T) :
    pullback M (𝟙 T) q = q :=
  Subtype.ext (Paired.PELFunctor.PairedPELClasses.pullback_id q.val)

theorem pullback_comp (f : U ⟶ T) (h : V ⟶ U)
    (q : TypedPairedPELClasses P iota N n M T) :
    pullback M (h ≫ f) q = pullback M h (pullback M f q) :=
  Subtype.ext (Paired.PELFunctor.PairedPELClasses.pullback_comp f h q.val)

def swap [CharZero K] (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    TypedPairedPELClasses P iota N n M T → TypedPairedPELClasses P iota N n M T :=
  fun q => ⟨Paired.PELFunctor.PairedPELClasses.swap q.val,
    (Paired.PELFunctor.PairedPELClasses.hasKernelType_swap_iff M hn hdegree q.val).mpr q.property⟩

theorem swap_swap [CharZero K] (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (q : TypedPairedPELClasses P iota N n M T) :
    swap M hn hdegree (swap M hn hdegree q) = q :=
  Subtype.ext (Paired.PELFunctor.PairedPELClasses.swap_swap q.val)

theorem pullback_swap [CharZero K] (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (f : U ⟶ T) (q : TypedPairedPELClasses P iota N n M T) :
    pullback M f (swap M hn hdegree q) = swap M hn hdegree (pullback M f q) :=
  Subtype.ext (Paired.PELFunctor.PairedPELClasses.pullback_swap f q.val)

end TypedPairedPEL.TypedPairedPELClasses

def TypedPairedPEL.typedPairedPELModuliFunctor (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N n : ℕ) (M : Type) [AddCommGroup M] :
    (Over (Spec (.of K)))ᵒᵖ ⥤ Type 1 where
  obj T := TypedPairedPEL.TypedPairedPELClasses P iota N n M T.unop
  map f := TypeCat.ofHom (TypedPairedPEL.TypedPairedPELClasses.pullback M f.unop)
  map_id _ := by
    ext q
    exact TypedPairedPEL.TypedPairedPELClasses.pullback_id M q
  map_comp f h := by
    ext q
    exact TypedPairedPEL.TypedPairedPELClasses.pullback_comp M f.unop h.unop q

def TypedPairedPEL.typedPairedPELForget :
    TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M ⟶ Paired.PELFunctor.pairedPELModuliFunctor P iota N n where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

def TypedPairedPEL.typedPairedPELSource : TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M ⟶ PEL.Classifying.pelModuliFunctor P iota N :=
  TypedPairedPEL.typedPairedPELForget M ≫ Paired.PELFunctor.pairedPELSource

def TypedPairedPEL.typedPairedPELTarget : TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M ⟶ PEL.Classifying.pelModuliFunctor P iota N :=
  TypedPairedPEL.typedPairedPELForget M ≫ Paired.PELFunctor.pairedPELTarget

def TypedPairedPEL.typedPairedPELSwap [CharZero K] (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M ⟶ TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M where
  app _ := TypeCat.ofHom (TypedPairedPEL.TypedPairedPELClasses.swap M hn hdegree)
  naturality _ _ f := by
    ext q
    exact (TypedPairedPEL.TypedPairedPELClasses.pullback_swap M hn hdegree f.unop q).symm

theorem TypedPairedPEL.typedPairedPELSwap_involutive [CharZero K] (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    TypedPairedPEL.typedPairedPELSwap (P := P) (iota := iota) (N := N) M hn hdegree ≫
      TypedPairedPEL.typedPairedPELSwap M hn hdegree = 𝟙 _ := by
  ext T q
  exact TypedPairedPEL.TypedPairedPELClasses.swap_swap M hn hdegree q

theorem TypedPairedPEL.typedPairedPELSwap_source [CharZero K] (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    TypedPairedPEL.typedPairedPELSwap (P := P) (iota := iota) (N := N) M hn hdegree ≫
      TypedPairedPEL.typedPairedPELSource M = TypedPairedPEL.typedPairedPELTarget M := by
  ext T q
  exact Paired.PELFunctor.PairedPELClasses.source_swap q.val

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
