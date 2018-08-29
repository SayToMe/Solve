import { Component, OnInit } from '@angular/core';

@Component({
  selector: 'app-workspace',
  templateUrl: './workspace.component.html',
  styleUrls: ['./workspace.component.scss']
})
export class WorkspaceComponent implements OnInit {
  line = '';
  history = [];

  constructor() { }

  ngOnInit() {
  }

  onCommandRaised(line: string) {
    this.history.push(line);
    this.line = '';
  }
}
