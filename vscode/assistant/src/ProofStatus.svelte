<script lang="ts">
  export let status: SearchStatus;
</script>

{#if status.outcome === null}
  <pre>Working...</pre>
{:else if status.outcome === "Inconsistent"}
  <pre>Local assumptions are inconsistent.</pre>
  <pre>If this is a proof by contradiction, put a `false` at the end of this block.</pre>
  <pre>If there shouldn't be a contradiction, please report a bug!</pre>
{:else if status.steps === null}
  <pre>We could not find a proof.</pre>
{:else if status.code === null}
  <pre>Error during code generation:</pre>
  <pre>    {status.codeError}</pre>
{:else if !status.needsSimplification}
  <pre>The proposition follows trivially.</pre>
{:else if status.code.length === 0}
  <pre>We found a proof, but it needs to be simplified, and we couldn't
       decide how to simplify it. Sorry!</pre>
{:else}
  <pre>{["The proof needs to be simplified. Try this:\n"]
      .concat(status.code)
      .join("\n\t")
      .replace(/\t/g, "\u00A0".repeat(4))}</pre>
  <button on:click>Insert code</button>
{/if}
