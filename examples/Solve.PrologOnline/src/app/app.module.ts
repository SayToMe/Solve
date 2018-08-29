import { BrowserModule } from '@angular/platform-browser';
import { NgModule } from '@angular/core';

import { AppComponent } from './app.component';
import { WorkspaceComponent } from './workspace/workspace.component';
import { HeaderComponent } from './header/header.component';
import { CommandLineComponent } from './command-line/command-line.component';
import { CommandHistoryComponent } from './command-history/command-history.component';
import { StoreModule } from '@ngrx/store';
import { counterReducer } from './state/reducers';

@NgModule({
  declarations: [
    AppComponent,
    WorkspaceComponent,
    HeaderComponent,
    CommandLineComponent,
    CommandHistoryComponent,
  ],
  imports: [
    BrowserModule,
    StoreModule.forRoot({ count: counterReducer })
  ],
  providers: [],
  bootstrap: [AppComponent]
})
export class AppModule { }
