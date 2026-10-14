<script lang="ts">
  export let status: SearchStatus;
</script>

{#if status.outcome === null}
  <p>Working...</p>
{:else if status.outcome === "Inconsistent"}
  <p>Local assumptions are inconsistent.</p>
  <p>If this is a proof by contradiction, put a `false` at the end of this block.</p>
  <p>If there shouldn't be a contradiction, please report a bug!</p>
{:else if status.steps === null}
  <p>We could not find a proof.</p>
{:else if status.code === null}
  <p>Error during code generation:</p>
  <div class="proof-code">{status.codeError}</div>
{:else if !status.needsSimplification}
  <p>The proposition follows trivially.</p>
{:else if status.code.length === 0}
  <p>We found a proof, but it needs to be simplified, and we couldn't
       decide how to simplify it. Sorry!</p>
{:else}
  <p>The proof needs to be simplified. Try this:</p>
  <div class="proof-code">{status.code.join("\n")}</div>
  <button on:click>Insert code</button>
{/if}

<style>
  .proof-code {
    white-space: pre-wrap;
    overflow-wrap: anywhere;
    padding-inline-start: 4ch;
    tab-size: 4;
  }
</style>
