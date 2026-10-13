<!-- Modified for Venticorn: CSS-based clause and premise spacing. -->
<script lang="ts">
  export let step: ProofStepInfo;
  export let clauseClick: (id: number) => void;
  export let showLocation: (uri: string, range: Range) => void;
  import Clause from "./Clause.svelte";
  import Rule from "./Rule.svelte";
</script>

{#if step.clause.text === null}
  Contradiction, depth {step.depth}, <Rule {step} {showLocation} />.<br />
{:else if step.clause.id === null}
  An unactivated clause, depth {step.depth}, <Rule {step} {showLocation} />:<br
  />
  <Clause clause={step.clause} />
{:else}
  Clause {step.clause.id}, depth {step.depth},
  <Rule {step} {showLocation} />:<br />
  <Clause clause={step.clause} onClick={clauseClick} />
{/if}
{#each step.premises as [desc, clause]}
  <span class="premise">using
    {#if clause.id !== null}
      clause {clause.id} as
    {/if}
    {desc}:</span>
  <Clause {clause} onClick={clauseClick} />
{/each}
