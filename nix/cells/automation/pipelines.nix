{
  inputs,
  cell,
}: {
  ci = {config, lib, ...}: {
    preset = {
      nix.enable = true;

      github-ci = {
        # Tullia tasks can run locally or on Cicero.
        # When no facts are present we know that we are running locally and vice versa.
        # When running locally, the current directory is already bind-mounted into the container,
        # so we don't need to fetch the source from GitHub and we don't want to report a GitHub status.
        enable = config.actionRun.facts != {};
        repo = "input-output-hk/ouroboros-network";
        sha = config.preset.github-ci.lib.readRevision inputs.cells.cloud.library.actionCiInputName null;
      };
    };

    command.text = let
      inherit (inputs.nixpkgs) system;
    in ''
      nix build -L .#hydraJobs.${lib.escapeShellArg system}.required
    '';

    memory = 1024 * 8;
    nomad.resources.cpu = 10000;
  };
}
