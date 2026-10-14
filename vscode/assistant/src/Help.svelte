<script lang="ts">
  export let help: AssistantHelp = { state: "inactive" };
</script>

{#if help.state === "inactive"}
  <h1 class="header">Venticorn Assistant</h1>
  <p>Open an Acorn file, or create a new file with the .ac extension.</p>
{:else if help.state === "newDocument"}
  <h1 class="header">Start a proof</h1>
  <p>Enter a theorem, then save the file with the .ac extension to verify it.</p>
{:else if help.state === "unsaved"}
  <h1 class="header">Save your changes</h1>
  <p>Save this file before searching for a proof. Earlier results have been cleared.</p>
{:else}
  <h1 class="header">Select a proposition to see its proof.</h1>
{/if}
